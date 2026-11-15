import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0316
import HodgeLean.Foundations.Program.G32PropFourSixPacked0315

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_015 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 15 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_015_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 16 8 9, g32p_row03_traceSegment_015_0016_0008, g32p_row03_traceSegment_015_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 0 16 17, g32p_row03_traceSegment_015_0000_0016, g32p_row03_traceSegment_015_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 33 8 9, g32p_row03_traceSegment_015_0033_0008, g32p_row03_traceSegment_015_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 50 8 9, g32p_row03_traceSegment_015_0050_0008, g32p_row03_traceSegment_015_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 33 17 17, g32p_row03_traceSegment_015_0033_0017, g32p_row03_traceSegment_015_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 0 33 34, g32p_row03_traceSegment_015_0000_0033, g32p_row03_traceSegment_015_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 67 8 9, g32p_row03_traceSegment_015_0067_0008, g32p_row03_traceSegment_015_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 84 8 9, g32p_row03_traceSegment_015_0084_0008, g32p_row03_traceSegment_015_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 67 17 17, g32p_row03_traceSegment_015_0067_0017, g32p_row03_traceSegment_015_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 101 8 9, g32p_row03_traceSegment_015_0101_0008, g32p_row03_traceSegment_015_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 118 8 9, g32p_row03_traceSegment_015_0118_0008, g32p_row03_traceSegment_015_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 101 17 17, g32p_row03_traceSegment_015_0101_0017, g32p_row03_traceSegment_015_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 67 34 34, g32p_row03_traceSegment_015_0067_0034, g32p_row03_traceSegment_015_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 0 67 68, g32p_row03_traceSegment_015_0000_0067, g32p_row03_traceSegment_015_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 151 8 9, g32p_row03_traceSegment_015_0151_0008, g32p_row03_traceSegment_015_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 135 16 17, g32p_row03_traceSegment_015_0135_0016, g32p_row03_traceSegment_015_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 168 8 9, g32p_row03_traceSegment_015_0168_0008, g32p_row03_traceSegment_015_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 185 8 9, g32p_row03_traceSegment_015_0185_0008, g32p_row03_traceSegment_015_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 168 17 17, g32p_row03_traceSegment_015_0168_0017, g32p_row03_traceSegment_015_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 135 33 34, g32p_row03_traceSegment_015_0135_0033, g32p_row03_traceSegment_015_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 202 8 9, g32p_row03_traceSegment_015_0202_0008, g32p_row03_traceSegment_015_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 219 8 9, g32p_row03_traceSegment_015_0219_0008, g32p_row03_traceSegment_015_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 202 17 17, g32p_row03_traceSegment_015_0202_0017, g32p_row03_traceSegment_015_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 244 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 236 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 236 8 9, g32p_row03_traceSegment_015_0236_0008, g32p_row03_traceSegment_015_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 253 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 253 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 253 8 9, g32p_row03_traceSegment_015_0253_0008, g32p_row03_traceSegment_015_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 236 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 236 17 17, g32p_row03_traceSegment_015_0236_0017, g32p_row03_traceSegment_015_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 202 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 202 34 34, g32p_row03_traceSegment_015_0202_0034, g32p_row03_traceSegment_015_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 135 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 135 67 68, g32p_row03_traceSegment_015_0135_0067, g32p_row03_traceSegment_015_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 0 270 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 0 135 135, g32p_row03_traceSegment_015_0000_0135, g32p_row03_traceSegment_015_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 270 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 286 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 286 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 286 8 9, g32p_row03_traceSegment_015_0286_0008, g32p_row03_traceSegment_015_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 270 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 270 16 17, g32p_row03_traceSegment_015_0270_0016, g32p_row03_traceSegment_015_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 303 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 303 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 303 8 9, g32p_row03_traceSegment_015_0303_0008, g32p_row03_traceSegment_015_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 320 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 328 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 320 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 320 8 9, g32p_row03_traceSegment_015_0320_0008, g32p_row03_traceSegment_015_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 303 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 303 17 17, g32p_row03_traceSegment_015_0303_0017, g32p_row03_traceSegment_015_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 270 67 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 270 33 34, g32p_row03_traceSegment_015_0270_0033, g32p_row03_traceSegment_015_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 337 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 345 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 337 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 337 8 9, g32p_row03_traceSegment_015_0337_0008, g32p_row03_traceSegment_015_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 354 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 362 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 354 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 354 8 9, g32p_row03_traceSegment_015_0354_0008, g32p_row03_traceSegment_015_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 337 34 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 337 17 17, g32p_row03_traceSegment_015_0337_0017, g32p_row03_traceSegment_015_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 371 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 379 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 371 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 371 8 9, g32p_row03_traceSegment_015_0371_0008, g32p_row03_traceSegment_015_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 388 8 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 388 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 388 8 9, g32p_row03_traceSegment_015_0388_0008, g32p_row03_traceSegment_015_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 371 34 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 371 17 17, g32p_row03_traceSegment_015_0371_0017, g32p_row03_traceSegment_015_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 337 68 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 337 34 34, g32p_row03_traceSegment_015_0337_0034, g32p_row03_traceSegment_015_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 270 135 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 270 67 68, g32p_row03_traceSegment_015_0270_0067, g32p_row03_traceSegment_015_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 421 8 9, g32p_row03_traceSegment_015_0421_0008, g32p_row03_traceSegment_015_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 405 16 17, g32p_row03_traceSegment_015_0405_0016, g32p_row03_traceSegment_015_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 438 8 9, g32p_row03_traceSegment_015_0438_0008, g32p_row03_traceSegment_015_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 455 8 9, g32p_row03_traceSegment_015_0455_0008, g32p_row03_traceSegment_015_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 438 17 17, g32p_row03_traceSegment_015_0438_0017, g32p_row03_traceSegment_015_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 405 33 34, g32p_row03_traceSegment_015_0405_0033, g32p_row03_traceSegment_015_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 472 8 9, g32p_row03_traceSegment_015_0472_0008, g32p_row03_traceSegment_015_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 489 8 9, g32p_row03_traceSegment_015_0489_0008, g32p_row03_traceSegment_015_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 472 17 17, g32p_row03_traceSegment_015_0472_0017, g32p_row03_traceSegment_015_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 506 8 9, g32p_row03_traceSegment_015_0506_0008, g32p_row03_traceSegment_015_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 523 8 9, g32p_row03_traceSegment_015_0523_0008, g32p_row03_traceSegment_015_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 506 17 17, g32p_row03_traceSegment_015_0506_0017, g32p_row03_traceSegment_015_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 472 34 34, g32p_row03_traceSegment_015_0472_0034, g32p_row03_traceSegment_015_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 405 67 68, g32p_row03_traceSegment_015_0405_0067, g32p_row03_traceSegment_015_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 270 270 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 270 135 135, g32p_row03_traceSegment_015_0270_0135, g32p_row03_traceSegment_015_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_015 0 540 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 0 270 270, g32p_row03_traceSegment_015_0000_0270, g32p_row03_traceSegment_015_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 556 8 9, g32p_row03_traceSegment_015_0556_0008, g32p_row03_traceSegment_015_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 540 16 17, g32p_row03_traceSegment_015_0540_0016, g32p_row03_traceSegment_015_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 573 8 9, g32p_row03_traceSegment_015_0573_0008, g32p_row03_traceSegment_015_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 590 8 9, g32p_row03_traceSegment_015_0590_0008, g32p_row03_traceSegment_015_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 573 17 17, g32p_row03_traceSegment_015_0573_0017, g32p_row03_traceSegment_015_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 540 33 34, g32p_row03_traceSegment_015_0540_0033, g32p_row03_traceSegment_015_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 607 8 9, g32p_row03_traceSegment_015_0607_0008, g32p_row03_traceSegment_015_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 624 8 9, g32p_row03_traceSegment_015_0624_0008, g32p_row03_traceSegment_015_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 607 17 17, g32p_row03_traceSegment_015_0607_0017, g32p_row03_traceSegment_015_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 641 8 9, g32p_row03_traceSegment_015_0641_0008, g32p_row03_traceSegment_015_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 658 8 9, g32p_row03_traceSegment_015_0658_0008, g32p_row03_traceSegment_015_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 641 17 17, g32p_row03_traceSegment_015_0641_0017, g32p_row03_traceSegment_015_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 607 34 34, g32p_row03_traceSegment_015_0607_0034, g32p_row03_traceSegment_015_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 540 67 68, g32p_row03_traceSegment_015_0540_0067, g32p_row03_traceSegment_015_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 691 8 9, g32p_row03_traceSegment_015_0691_0008, g32p_row03_traceSegment_015_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 675 16 17, g32p_row03_traceSegment_015_0675_0016, g32p_row03_traceSegment_015_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 708 8 9, g32p_row03_traceSegment_015_0708_0008, g32p_row03_traceSegment_015_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 725 8 9, g32p_row03_traceSegment_015_0725_0008, g32p_row03_traceSegment_015_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 708 17 17, g32p_row03_traceSegment_015_0708_0017, g32p_row03_traceSegment_015_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 675 33 34, g32p_row03_traceSegment_015_0675_0033, g32p_row03_traceSegment_015_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 742 8 9, g32p_row03_traceSegment_015_0742_0008, g32p_row03_traceSegment_015_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 759 8 9, g32p_row03_traceSegment_015_0759_0008, g32p_row03_traceSegment_015_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 742 17 17, g32p_row03_traceSegment_015_0742_0017, g32p_row03_traceSegment_015_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 784 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 776 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 776 8 9, g32p_row03_traceSegment_015_0776_0008, g32p_row03_traceSegment_015_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 793 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 793 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 793 8 9, g32p_row03_traceSegment_015_0793_0008, g32p_row03_traceSegment_015_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 776 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 776 17 17, g32p_row03_traceSegment_015_0776_0017, g32p_row03_traceSegment_015_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 742 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 742 34 34, g32p_row03_traceSegment_015_0742_0034, g32p_row03_traceSegment_015_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 675 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 675 67 68, g32p_row03_traceSegment_015_0675_0067, g32p_row03_traceSegment_015_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 540 270 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 540 135 135, g32p_row03_traceSegment_015_0540_0135, g32p_row03_traceSegment_015_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 826 8 9, g32p_row03_traceSegment_015_0826_0008, g32p_row03_traceSegment_015_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 810 16 17, g32p_row03_traceSegment_015_0810_0016, g32p_row03_traceSegment_015_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 843 8 9, g32p_row03_traceSegment_015_0843_0008, g32p_row03_traceSegment_015_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 860 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 860 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 860 8 9, g32p_row03_traceSegment_015_0860_0008, g32p_row03_traceSegment_015_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 843 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 843 17 17, g32p_row03_traceSegment_015_0843_0017, g32p_row03_traceSegment_015_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 810 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 810 33 34, g32p_row03_traceSegment_015_0810_0033, g32p_row03_traceSegment_015_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 885 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 877 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 877 8 9, g32p_row03_traceSegment_015_0877_0008, g32p_row03_traceSegment_015_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 894 8 9, g32p_row03_traceSegment_015_0894_0008, g32p_row03_traceSegment_015_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 877 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 877 17 17, g32p_row03_traceSegment_015_0877_0017, g32p_row03_traceSegment_015_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 911 8 9, g32p_row03_traceSegment_015_0911_0008, g32p_row03_traceSegment_015_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 928 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 928 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 928 8 9, g32p_row03_traceSegment_015_0928_0008, g32p_row03_traceSegment_015_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 911 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 911 17 17, g32p_row03_traceSegment_015_0911_0017, g32p_row03_traceSegment_015_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 877 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 877 34 34, g32p_row03_traceSegment_015_0877_0034, g32p_row03_traceSegment_015_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 810 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 810 67 68, g32p_row03_traceSegment_015_0810_0067, g32p_row03_traceSegment_015_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 945 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 961 8 9, g32p_row03_traceSegment_015_0961_0008, g32p_row03_traceSegment_015_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 945 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 945 16 17, g32p_row03_traceSegment_015_0945_0016, g32p_row03_traceSegment_015_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 978 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 978 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 978 8 9, g32p_row03_traceSegment_015_0978_0008, g32p_row03_traceSegment_015_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1003 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 995 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 995 8 9, g32p_row03_traceSegment_015_0995_0008, g32p_row03_traceSegment_015_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 978 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 978 17 17, g32p_row03_traceSegment_015_0978_0017, g32p_row03_traceSegment_015_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 945 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 945 33 34, g32p_row03_traceSegment_015_0945_0033, g32p_row03_traceSegment_015_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1020 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1012 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1012 8 9, g32p_row03_traceSegment_015_1012_0008, g32p_row03_traceSegment_015_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1029 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1029 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1029 8 9, g32p_row03_traceSegment_015_1029_0008, g32p_row03_traceSegment_015_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1012 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1012 17 17, g32p_row03_traceSegment_015_1012_0017, g32p_row03_traceSegment_015_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1046 8 9, g32p_row03_traceSegment_015_1046_0008, g32p_row03_traceSegment_015_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1071 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1063 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1063 8 9, g32p_row03_traceSegment_015_1063_0008, g32p_row03_traceSegment_015_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1046 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1046 17 17, g32p_row03_traceSegment_015_1046_0017, g32p_row03_traceSegment_015_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 1012 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1012 34 34, g32p_row03_traceSegment_015_1012_0034, g32p_row03_traceSegment_015_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 945 135 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 945 67 68, g32p_row03_traceSegment_015_0945_0067, g32p_row03_traceSegment_015_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 810 270 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 810 135 135, g32p_row03_traceSegment_015_0810_0135, g32p_row03_traceSegment_015_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_015 540 540 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 540 270 270, g32p_row03_traceSegment_015_0540_0270, g32p_row03_traceSegment_015_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_015 0 1080 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 0 540 540, g32p_row03_traceSegment_015_0000_0540, g32p_row03_traceSegment_015_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1096 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1104 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1096 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1096 8 9, g32p_row03_traceSegment_015_1096_0008, g32p_row03_traceSegment_015_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 1080 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1080 16 17, g32p_row03_traceSegment_015_1080_0016, g32p_row03_traceSegment_015_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1113 8 9, g32p_row03_traceSegment_015_1113_0008, g32p_row03_traceSegment_015_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1130 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1130 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1130 8 9, g32p_row03_traceSegment_015_1130_0008, g32p_row03_traceSegment_015_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1113 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1113 17 17, g32p_row03_traceSegment_015_1113_0017, g32p_row03_traceSegment_015_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 1080 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1080 33 34, g32p_row03_traceSegment_015_1080_0033, g32p_row03_traceSegment_015_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1147 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1147 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1147 8 9, g32p_row03_traceSegment_015_1147_0008, g32p_row03_traceSegment_015_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1164 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1164 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1164 8 9, g32p_row03_traceSegment_015_1164_0008, g32p_row03_traceSegment_015_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1147 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1147 17 17, g32p_row03_traceSegment_015_1147_0017, g32p_row03_traceSegment_015_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1181 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1181 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1181 8 9, g32p_row03_traceSegment_015_1181_0008, g32p_row03_traceSegment_015_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1198 8 9, g32p_row03_traceSegment_015_1198_0008, g32p_row03_traceSegment_015_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1181 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1181 17 17, g32p_row03_traceSegment_015_1181_0017, g32p_row03_traceSegment_015_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 1147 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1147 34 34, g32p_row03_traceSegment_015_1147_0034, g32p_row03_traceSegment_015_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 1080 135 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1080 67 68, g32p_row03_traceSegment_015_1080_0067, g32p_row03_traceSegment_015_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 1215 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1231 8 9, g32p_row03_traceSegment_015_1231_0008, g32p_row03_traceSegment_015_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 1215 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1215 16 17, g32p_row03_traceSegment_015_1215_0016, g32p_row03_traceSegment_015_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1248 8 9, g32p_row03_traceSegment_015_1248_0008, g32p_row03_traceSegment_015_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1265 8 9, g32p_row03_traceSegment_015_1265_0008, g32p_row03_traceSegment_015_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1248 17 17, g32p_row03_traceSegment_015_1248_0017, g32p_row03_traceSegment_015_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 1215 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1215 33 34, g32p_row03_traceSegment_015_1215_0033, g32p_row03_traceSegment_015_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1282 8 9, g32p_row03_traceSegment_015_1282_0008, g32p_row03_traceSegment_015_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1299 8 9, g32p_row03_traceSegment_015_1299_0008, g32p_row03_traceSegment_015_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1282 17 17, g32p_row03_traceSegment_015_1282_0017, g32p_row03_traceSegment_015_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1316 8 9, g32p_row03_traceSegment_015_1316_0008, g32p_row03_traceSegment_015_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1333 8 9, g32p_row03_traceSegment_015_1333_0008, g32p_row03_traceSegment_015_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1316 17 17, g32p_row03_traceSegment_015_1316_0017, g32p_row03_traceSegment_015_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1282 34 34, g32p_row03_traceSegment_015_1282_0034, g32p_row03_traceSegment_015_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 1215 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1215 67 68, g32p_row03_traceSegment_015_1215_0067, g32p_row03_traceSegment_015_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 1080 270 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1080 135 135, g32p_row03_traceSegment_015_1080_0135, g32p_row03_traceSegment_015_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1366 8 9, g32p_row03_traceSegment_015_1366_0008, g32p_row03_traceSegment_015_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1350 16 17, g32p_row03_traceSegment_015_1350_0016, g32p_row03_traceSegment_015_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1383 8 9, g32p_row03_traceSegment_015_1383_0008, g32p_row03_traceSegment_015_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1400 8 9, g32p_row03_traceSegment_015_1400_0008, g32p_row03_traceSegment_015_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1383 17 17, g32p_row03_traceSegment_015_1383_0017, g32p_row03_traceSegment_015_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1350 33 34, g32p_row03_traceSegment_015_1350_0033, g32p_row03_traceSegment_015_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1425 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1417 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1417 8 9, g32p_row03_traceSegment_015_1417_0008, g32p_row03_traceSegment_015_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1434 8 9, g32p_row03_traceSegment_015_1434_0008, g32p_row03_traceSegment_015_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1417 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1417 17 17, g32p_row03_traceSegment_015_1417_0017, g32p_row03_traceSegment_015_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1451 8 9, g32p_row03_traceSegment_015_1451_0008, g32p_row03_traceSegment_015_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1468 8 9, g32p_row03_traceSegment_015_1468_0008, g32p_row03_traceSegment_015_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1451 17 17, g32p_row03_traceSegment_015_1451_0017, g32p_row03_traceSegment_015_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 1417 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1417 34 34, g32p_row03_traceSegment_015_1417_0034, g32p_row03_traceSegment_015_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 1350 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1350 67 68, g32p_row03_traceSegment_015_1350_0067, g32p_row03_traceSegment_015_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1501 8 9, g32p_row03_traceSegment_015_1501_0008, g32p_row03_traceSegment_015_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1485 16 17, g32p_row03_traceSegment_015_1485_0016, g32p_row03_traceSegment_015_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1518 8 9, g32p_row03_traceSegment_015_1518_0008, g32p_row03_traceSegment_015_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1535 8 9, g32p_row03_traceSegment_015_1535_0008, g32p_row03_traceSegment_015_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1518 17 17, g32p_row03_traceSegment_015_1518_0017, g32p_row03_traceSegment_015_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1485 33 34, g32p_row03_traceSegment_015_1485_0033, g32p_row03_traceSegment_015_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1552 8 9, g32p_row03_traceSegment_015_1552_0008, g32p_row03_traceSegment_015_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1569 8 9, g32p_row03_traceSegment_015_1569_0008, g32p_row03_traceSegment_015_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1552 17 17, g32p_row03_traceSegment_015_1552_0017, g32p_row03_traceSegment_015_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1594 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1586 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1586 8 9, g32p_row03_traceSegment_015_1586_0008, g32p_row03_traceSegment_015_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1603 8 9, g32p_row03_traceSegment_015_1603_0008, g32p_row03_traceSegment_015_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1586 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1586 17 17, g32p_row03_traceSegment_015_1586_0017, g32p_row03_traceSegment_015_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 1552 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1552 34 34, g32p_row03_traceSegment_015_1552_0034, g32p_row03_traceSegment_015_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 1485 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1485 67 68, g32p_row03_traceSegment_015_1485_0067, g32p_row03_traceSegment_015_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 1350 270 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1350 135 135, g32p_row03_traceSegment_015_1350_0135, g32p_row03_traceSegment_015_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_015 1080 540 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1080 270 270, g32p_row03_traceSegment_015_1080_0270, g32p_row03_traceSegment_015_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1636 8 9, g32p_row03_traceSegment_015_1636_0008, g32p_row03_traceSegment_015_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1620 16 17, g32p_row03_traceSegment_015_1620_0016, g32p_row03_traceSegment_015_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1653 8 9, g32p_row03_traceSegment_015_1653_0008, g32p_row03_traceSegment_015_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1670 8 9, g32p_row03_traceSegment_015_1670_0008, g32p_row03_traceSegment_015_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1653 17 17, g32p_row03_traceSegment_015_1653_0017, g32p_row03_traceSegment_015_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1620 33 34, g32p_row03_traceSegment_015_1620_0033, g32p_row03_traceSegment_015_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1687 8 9, g32p_row03_traceSegment_015_1687_0008, g32p_row03_traceSegment_015_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1704 8 9, g32p_row03_traceSegment_015_1704_0008, g32p_row03_traceSegment_015_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1687 17 17, g32p_row03_traceSegment_015_1687_0017, g32p_row03_traceSegment_015_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1729 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1721 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1721 8 9, g32p_row03_traceSegment_015_1721_0008, g32p_row03_traceSegment_015_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1738 8 9, g32p_row03_traceSegment_015_1738_0008, g32p_row03_traceSegment_015_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1721 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1721 17 17, g32p_row03_traceSegment_015_1721_0017, g32p_row03_traceSegment_015_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 1687 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1687 34 34, g32p_row03_traceSegment_015_1687_0034, g32p_row03_traceSegment_015_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 1620 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1620 67 68, g32p_row03_traceSegment_015_1620_0067, g32p_row03_traceSegment_015_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1771 8 9, g32p_row03_traceSegment_015_1771_0008, g32p_row03_traceSegment_015_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1755 16 17, g32p_row03_traceSegment_015_1755_0016, g32p_row03_traceSegment_015_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1788 8 9, g32p_row03_traceSegment_015_1788_0008, g32p_row03_traceSegment_015_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1813 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1805 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1805 8 9, g32p_row03_traceSegment_015_1805_0008, g32p_row03_traceSegment_015_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1788 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1788 17 17, g32p_row03_traceSegment_015_1788_0017, g32p_row03_traceSegment_015_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 1755 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1755 33 34, g32p_row03_traceSegment_015_1755_0033, g32p_row03_traceSegment_015_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1822 8 9, g32p_row03_traceSegment_015_1822_0008, g32p_row03_traceSegment_015_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1839 8 9, g32p_row03_traceSegment_015_1839_0008, g32p_row03_traceSegment_015_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1822 17 17, g32p_row03_traceSegment_015_1822_0017, g32p_row03_traceSegment_015_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1856 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1856 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1856 8 9, g32p_row03_traceSegment_015_1856_0008, g32p_row03_traceSegment_015_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1873 8 9, g32p_row03_traceSegment_015_1873_0008, g32p_row03_traceSegment_015_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1856 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1856 17 17, g32p_row03_traceSegment_015_1856_0017, g32p_row03_traceSegment_015_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 1822 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1822 34 34, g32p_row03_traceSegment_015_1822_0034, g32p_row03_traceSegment_015_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 1755 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1755 67 68, g32p_row03_traceSegment_015_1755_0067, g32p_row03_traceSegment_015_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 1620 270 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1620 135 135, g32p_row03_traceSegment_015_1620_0135, g32p_row03_traceSegment_015_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 1890 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1906 8 9, g32p_row03_traceSegment_015_1906_0008, g32p_row03_traceSegment_015_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 1890 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1890 16 17, g32p_row03_traceSegment_015_1890_0016, g32p_row03_traceSegment_015_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1931 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1923 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1923 8 9, g32p_row03_traceSegment_015_1923_0008, g32p_row03_traceSegment_015_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1940 8 9, g32p_row03_traceSegment_015_1940_0008, g32p_row03_traceSegment_015_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1923 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1923 17 17, g32p_row03_traceSegment_015_1923_0017, g32p_row03_traceSegment_015_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 1890 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1890 33 34, g32p_row03_traceSegment_015_1890_0033, g32p_row03_traceSegment_015_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1965 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1957 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1957 8 9, g32p_row03_traceSegment_015_1957_0008, g32p_row03_traceSegment_015_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1982 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1974 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1974 8 9, g32p_row03_traceSegment_015_1974_0008, g32p_row03_traceSegment_015_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1957 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1957 17 17, g32p_row03_traceSegment_015_1957_0017, g32p_row03_traceSegment_015_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1991 8 9, g32p_row03_traceSegment_015_1991_0008, g32p_row03_traceSegment_015_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2008 8 9, g32p_row03_traceSegment_015_2008_0008, g32p_row03_traceSegment_015_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1991 17 17, g32p_row03_traceSegment_015_1991_0017, g32p_row03_traceSegment_015_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 1957 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1957 34 34, g32p_row03_traceSegment_015_1957_0034, g32p_row03_traceSegment_015_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 1890 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1890 67 68, g32p_row03_traceSegment_015_1890_0067, g32p_row03_traceSegment_015_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2049 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2041 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2041 8 9, g32p_row03_traceSegment_015_2041_0008, g32p_row03_traceSegment_015_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 2025 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2025 16 17, g32p_row03_traceSegment_015_2025_0016, g32p_row03_traceSegment_015_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2066 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2058 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2058 8 9, g32p_row03_traceSegment_015_2058_0008, g32p_row03_traceSegment_015_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2075 8 9, g32p_row03_traceSegment_015_2075_0008, g32p_row03_traceSegment_015_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2058 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2058 17 17, g32p_row03_traceSegment_015_2058_0017, g32p_row03_traceSegment_015_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 2025 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2025 33 34, g32p_row03_traceSegment_015_2025_0033, g32p_row03_traceSegment_015_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2092 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2100 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2092 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2092 8 9, g32p_row03_traceSegment_015_2092_0008, g32p_row03_traceSegment_015_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2109 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2117 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2109 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2109 8 9, g32p_row03_traceSegment_015_2109_0008, g32p_row03_traceSegment_015_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2092 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2092 17 17, g32p_row03_traceSegment_015_2092_0017, g32p_row03_traceSegment_015_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2126 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2126 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2126 8 9, g32p_row03_traceSegment_015_2126_0008, g32p_row03_traceSegment_015_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2143 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2143 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2143 8 9, g32p_row03_traceSegment_015_2143_0008, g32p_row03_traceSegment_015_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2126 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2126 17 17, g32p_row03_traceSegment_015_2126_0017, g32p_row03_traceSegment_015_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 2092 68 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2092 34 34, g32p_row03_traceSegment_015_2092_0034, g32p_row03_traceSegment_015_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 2025 135 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2025 67 68, g32p_row03_traceSegment_015_2025_0067, g32p_row03_traceSegment_015_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 1890 270 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1890 135 135, g32p_row03_traceSegment_015_1890_0135, g32p_row03_traceSegment_015_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_015 1620 540 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1620 270 270, g32p_row03_traceSegment_015_1620_0270, g32p_row03_traceSegment_015_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_015_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_015 1080 1080 = [0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 1080 540 540, g32p_row03_traceSegment_015_1080_0540, g32p_row03_traceSegment_015_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_015 0 2160 = [0, 55] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 0 1080 1080, g32p_row03_traceSegment_015_0000_1080, g32p_row03_traceSegment_015_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 2160 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2184 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2176 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2176 8 9, g32p_row03_traceSegment_015_2176_0008, g32p_row03_traceSegment_015_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 2160 33 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2160 16 17, g32p_row03_traceSegment_015_2160_0016, g32p_row03_traceSegment_015_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2201 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2193 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2193 8 9, g32p_row03_traceSegment_015_2193_0008, g32p_row03_traceSegment_015_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2218 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2210 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2210 8 9, g32p_row03_traceSegment_015_2210_0008, g32p_row03_traceSegment_015_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2193 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2193 17 17, g32p_row03_traceSegment_015_2193_0017, g32p_row03_traceSegment_015_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 2160 67 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2160 33 34, g32p_row03_traceSegment_015_2160_0033, g32p_row03_traceSegment_015_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2235 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2227 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2227 8 9, g32p_row03_traceSegment_015_2227_0008, g32p_row03_traceSegment_015_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2244 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2252 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2244 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2244 8 9, g32p_row03_traceSegment_015_2244_0008, g32p_row03_traceSegment_015_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2227 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2227 17 17, g32p_row03_traceSegment_015_2227_0017, g32p_row03_traceSegment_015_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2261 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2269 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2261 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2261 8 9, g32p_row03_traceSegment_015_2261_0008, g32p_row03_traceSegment_015_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2278 8 9, g32p_row03_traceSegment_015_2278_0008, g32p_row03_traceSegment_015_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2261 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2261 17 17, g32p_row03_traceSegment_015_2261_0017, g32p_row03_traceSegment_015_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 2227 68 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2227 34 34, g32p_row03_traceSegment_015_2227_0034, g32p_row03_traceSegment_015_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 2160 135 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2160 67 68, g32p_row03_traceSegment_015_2160_0067, g32p_row03_traceSegment_015_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2311 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2311 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2311 8 9, g32p_row03_traceSegment_015_2311_0008, g32p_row03_traceSegment_015_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 2295 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2295 16 17, g32p_row03_traceSegment_015_2295_0016, g32p_row03_traceSegment_015_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2328 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2336 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2328 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2328 8 9, g32p_row03_traceSegment_015_2328_0008, g32p_row03_traceSegment_015_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2345 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2345 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2345 8 9, g32p_row03_traceSegment_015_2345_0008, g32p_row03_traceSegment_015_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2328 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2328 17 17, g32p_row03_traceSegment_015_2328_0017, g32p_row03_traceSegment_015_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 2295 67 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2295 33 34, g32p_row03_traceSegment_015_2295_0033, g32p_row03_traceSegment_015_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2362 8 9, g32p_row03_traceSegment_015_2362_0008, g32p_row03_traceSegment_015_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2379 8 9, g32p_row03_traceSegment_015_2379_0008, g32p_row03_traceSegment_015_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2362 17 17, g32p_row03_traceSegment_015_2362_0017, g32p_row03_traceSegment_015_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2396 8 9, g32p_row03_traceSegment_015_2396_0008, g32p_row03_traceSegment_015_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2413 8 9, g32p_row03_traceSegment_015_2413_0008, g32p_row03_traceSegment_015_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2396 17 17, g32p_row03_traceSegment_015_2396_0017, g32p_row03_traceSegment_015_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2362 34 34, g32p_row03_traceSegment_015_2362_0034, g32p_row03_traceSegment_015_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 2295 135 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2295 67 68, g32p_row03_traceSegment_015_2295_0067, g32p_row03_traceSegment_015_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 2160 270 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2160 135 135, g32p_row03_traceSegment_015_2160_0135, g32p_row03_traceSegment_015_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2446 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2446 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2446 8 9, g32p_row03_traceSegment_015_2446_0008, g32p_row03_traceSegment_015_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 2430 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2430 16 17, g32p_row03_traceSegment_015_2430_0016, g32p_row03_traceSegment_015_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2463 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2463 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2463 8 9, g32p_row03_traceSegment_015_2463_0008, g32p_row03_traceSegment_015_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2480 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2480 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2480 8 9, g32p_row03_traceSegment_015_2480_0008, g32p_row03_traceSegment_015_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2463 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2463 17 17, g32p_row03_traceSegment_015_2463_0017, g32p_row03_traceSegment_015_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 2430 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2430 33 34, g32p_row03_traceSegment_015_2430_0033, g32p_row03_traceSegment_015_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2497 8 9, g32p_row03_traceSegment_015_2497_0008, g32p_row03_traceSegment_015_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2514 8 9, g32p_row03_traceSegment_015_2514_0008, g32p_row03_traceSegment_015_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2497 17 17, g32p_row03_traceSegment_015_2497_0017, g32p_row03_traceSegment_015_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2531 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2531 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2531 8 9, g32p_row03_traceSegment_015_2531_0008, g32p_row03_traceSegment_015_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2548 8 9, g32p_row03_traceSegment_015_2548_0008, g32p_row03_traceSegment_015_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2531 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2531 17 17, g32p_row03_traceSegment_015_2531_0017, g32p_row03_traceSegment_015_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 2497 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2497 34 34, g32p_row03_traceSegment_015_2497_0034, g32p_row03_traceSegment_015_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 2430 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2430 67 68, g32p_row03_traceSegment_015_2430_0067, g32p_row03_traceSegment_015_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 2565 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2581 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2589 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2581 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2581 8 9, g32p_row03_traceSegment_015_2581_0008, g32p_row03_traceSegment_015_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 2565 33 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2565 16 17, g32p_row03_traceSegment_015_2565_0016, g32p_row03_traceSegment_015_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2606 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2598 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2598 8 9, g32p_row03_traceSegment_015_2598_0008, g32p_row03_traceSegment_015_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2623 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2615 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2615 8 9, g32p_row03_traceSegment_015_2615_0008, g32p_row03_traceSegment_015_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2598 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2598 17 17, g32p_row03_traceSegment_015_2598_0017, g32p_row03_traceSegment_015_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 2565 67 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2565 33 34, g32p_row03_traceSegment_015_2565_0033, g32p_row03_traceSegment_015_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2632 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2632 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2632 8 9, g32p_row03_traceSegment_015_2632_0008, g32p_row03_traceSegment_015_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2649 8 9, g32p_row03_traceSegment_015_2649_0008, g32p_row03_traceSegment_015_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2632 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2632 17 17, g32p_row03_traceSegment_015_2632_0017, g32p_row03_traceSegment_015_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2666 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2666 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2666 8 9, g32p_row03_traceSegment_015_2666_0008, g32p_row03_traceSegment_015_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2683 8 9, g32p_row03_traceSegment_015_2683_0008, g32p_row03_traceSegment_015_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2666 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2666 17 17, g32p_row03_traceSegment_015_2666_0017, g32p_row03_traceSegment_015_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 2632 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2632 34 34, g32p_row03_traceSegment_015_2632_0034, g32p_row03_traceSegment_015_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 2565 135 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2565 67 68, g32p_row03_traceSegment_015_2565_0067, g32p_row03_traceSegment_015_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 2430 270 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2430 135 135, g32p_row03_traceSegment_015_2430_0135, g32p_row03_traceSegment_015_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_015 2160 540 = [0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2160 270 270, g32p_row03_traceSegment_015_2160_0270, g32p_row03_traceSegment_015_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2716 8 9, g32p_row03_traceSegment_015_2716_0008, g32p_row03_traceSegment_015_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2700 16 17, g32p_row03_traceSegment_015_2700_0016, g32p_row03_traceSegment_015_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2733 8 9, g32p_row03_traceSegment_015_2733_0008, g32p_row03_traceSegment_015_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2758 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2750 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2750 8 9, g32p_row03_traceSegment_015_2750_0008, g32p_row03_traceSegment_015_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2733 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2733 17 17, g32p_row03_traceSegment_015_2733_0017, g32p_row03_traceSegment_015_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 2700 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2700 33 34, g32p_row03_traceSegment_015_2700_0033, g32p_row03_traceSegment_015_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2775 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2767 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2767 8 9, g32p_row03_traceSegment_015_2767_0008, g32p_row03_traceSegment_015_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2784 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2784 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2784 8 9, g32p_row03_traceSegment_015_2784_0008, g32p_row03_traceSegment_015_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2767 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2767 17 17, g32p_row03_traceSegment_015_2767_0017, g32p_row03_traceSegment_015_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2809 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2801 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2801 8 9, g32p_row03_traceSegment_015_2801_0008, g32p_row03_traceSegment_015_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2818 8 9, g32p_row03_traceSegment_015_2818_0008, g32p_row03_traceSegment_015_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2801 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2801 17 17, g32p_row03_traceSegment_015_2801_0017, g32p_row03_traceSegment_015_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 2767 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2767 34 34, g32p_row03_traceSegment_015_2767_0034, g32p_row03_traceSegment_015_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 2700 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2700 67 68, g32p_row03_traceSegment_015_2700_0067, g32p_row03_traceSegment_015_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2851 8 9, g32p_row03_traceSegment_015_2851_0008, g32p_row03_traceSegment_015_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2835 16 17, g32p_row03_traceSegment_015_2835_0016, g32p_row03_traceSegment_015_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2876 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2868 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2868 8 9, g32p_row03_traceSegment_015_2868_0008, g32p_row03_traceSegment_015_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2885 8 9, g32p_row03_traceSegment_015_2885_0008, g32p_row03_traceSegment_015_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2868 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2868 17 17, g32p_row03_traceSegment_015_2868_0017, g32p_row03_traceSegment_015_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 2835 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2835 33 34, g32p_row03_traceSegment_015_2835_0033, g32p_row03_traceSegment_015_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2902 8 9, g32p_row03_traceSegment_015_2902_0008, g32p_row03_traceSegment_015_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2919 8 9, g32p_row03_traceSegment_015_2919_0008, g32p_row03_traceSegment_015_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2902 17 17, g32p_row03_traceSegment_015_2902_0017, g32p_row03_traceSegment_015_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2936 8 9, g32p_row03_traceSegment_015_2936_0008, g32p_row03_traceSegment_015_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2953 8 9, g32p_row03_traceSegment_015_2953_0008, g32p_row03_traceSegment_015_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2936 17 17, g32p_row03_traceSegment_015_2936_0017, g32p_row03_traceSegment_015_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2902 34 34, g32p_row03_traceSegment_015_2902_0034, g32p_row03_traceSegment_015_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 2835 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2835 67 68, g32p_row03_traceSegment_015_2835_0067, g32p_row03_traceSegment_015_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 2700 270 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2700 135 135, g32p_row03_traceSegment_015_2700_0135, g32p_row03_traceSegment_015_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2986 8 9, g32p_row03_traceSegment_015_2986_0008, g32p_row03_traceSegment_015_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2970 16 17, g32p_row03_traceSegment_015_2970_0016, g32p_row03_traceSegment_015_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3003 8 9, g32p_row03_traceSegment_015_3003_0008, g32p_row03_traceSegment_015_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3020 8 9, g32p_row03_traceSegment_015_3020_0008, g32p_row03_traceSegment_015_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3003 17 17, g32p_row03_traceSegment_015_3003_0017, g32p_row03_traceSegment_015_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2970 33 34, g32p_row03_traceSegment_015_2970_0033, g32p_row03_traceSegment_015_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3045 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3037 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3037 8 9, g32p_row03_traceSegment_015_3037_0008, g32p_row03_traceSegment_015_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3054 8 9, g32p_row03_traceSegment_015_3054_0008, g32p_row03_traceSegment_015_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3037 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3037 17 17, g32p_row03_traceSegment_015_3037_0017, g32p_row03_traceSegment_015_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3071 8 9, g32p_row03_traceSegment_015_3071_0008, g32p_row03_traceSegment_015_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3088 8 9, g32p_row03_traceSegment_015_3088_0008, g32p_row03_traceSegment_015_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3071 17 17, g32p_row03_traceSegment_015_3071_0017, g32p_row03_traceSegment_015_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 3037 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3037 34 34, g32p_row03_traceSegment_015_3037_0034, g32p_row03_traceSegment_015_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 2970 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2970 67 68, g32p_row03_traceSegment_015_2970_0067, g32p_row03_traceSegment_015_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3121 8 9, g32p_row03_traceSegment_015_3121_0008, g32p_row03_traceSegment_015_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3105 16 17, g32p_row03_traceSegment_015_3105_0016, g32p_row03_traceSegment_015_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3146 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3138 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3138 8 9, g32p_row03_traceSegment_015_3138_0008, g32p_row03_traceSegment_015_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3155 8 9, g32p_row03_traceSegment_015_3155_0008, g32p_row03_traceSegment_015_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3138 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3138 17 17, g32p_row03_traceSegment_015_3138_0017, g32p_row03_traceSegment_015_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 3105 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3105 33 34, g32p_row03_traceSegment_015_3105_0033, g32p_row03_traceSegment_015_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3172 8 9, g32p_row03_traceSegment_015_3172_0008, g32p_row03_traceSegment_015_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3189 8 9, g32p_row03_traceSegment_015_3189_0008, g32p_row03_traceSegment_015_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3172 17 17, g32p_row03_traceSegment_015_3172_0017, g32p_row03_traceSegment_015_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3206 8 9, g32p_row03_traceSegment_015_3206_0008, g32p_row03_traceSegment_015_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3231 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3223 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3223 8 9, g32p_row03_traceSegment_015_3223_0008, g32p_row03_traceSegment_015_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3206 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3206 17 17, g32p_row03_traceSegment_015_3206_0017, g32p_row03_traceSegment_015_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 3172 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3172 34 34, g32p_row03_traceSegment_015_3172_0034, g32p_row03_traceSegment_015_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 3105 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3105 67 68, g32p_row03_traceSegment_015_3105_0067, g32p_row03_traceSegment_015_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 2970 270 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2970 135 135, g32p_row03_traceSegment_015_2970_0135, g32p_row03_traceSegment_015_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_015 2700 540 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2700 270 270, g32p_row03_traceSegment_015_2700_0270, g32p_row03_traceSegment_015_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_015 2160 1080 = [0, 38] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2160 540 540, g32p_row03_traceSegment_015_2160_0540, g32p_row03_traceSegment_015_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 3240 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3256 8 9, g32p_row03_traceSegment_015_3256_0008, g32p_row03_traceSegment_015_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 3240 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3240 16 17, g32p_row03_traceSegment_015_3240_0016, g32p_row03_traceSegment_015_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3273 8 9, g32p_row03_traceSegment_015_3273_0008, g32p_row03_traceSegment_015_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3290 8 9, g32p_row03_traceSegment_015_3290_0008, g32p_row03_traceSegment_015_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3273 17 17, g32p_row03_traceSegment_015_3273_0017, g32p_row03_traceSegment_015_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 3240 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3240 33 34, g32p_row03_traceSegment_015_3240_0033, g32p_row03_traceSegment_015_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3307 8 9, g32p_row03_traceSegment_015_3307_0008, g32p_row03_traceSegment_015_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3324 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3324 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3324 8 9, g32p_row03_traceSegment_015_3324_0008, g32p_row03_traceSegment_015_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3307 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3307 17 17, g32p_row03_traceSegment_015_3307_0017, g32p_row03_traceSegment_015_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3341 8 9, g32p_row03_traceSegment_015_3341_0008, g32p_row03_traceSegment_015_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3358 8 9, g32p_row03_traceSegment_015_3358_0008, g32p_row03_traceSegment_015_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3341 17 17, g32p_row03_traceSegment_015_3341_0017, g32p_row03_traceSegment_015_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 3307 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3307 34 34, g32p_row03_traceSegment_015_3307_0034, g32p_row03_traceSegment_015_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 3240 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3240 67 68, g32p_row03_traceSegment_015_3240_0067, g32p_row03_traceSegment_015_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 3375 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3391 8 9, g32p_row03_traceSegment_015_3391_0008, g32p_row03_traceSegment_015_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 3375 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3375 16 17, g32p_row03_traceSegment_015_3375_0016, g32p_row03_traceSegment_015_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3408 8 9, g32p_row03_traceSegment_015_3408_0008, g32p_row03_traceSegment_015_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3425 8 9, g32p_row03_traceSegment_015_3425_0008, g32p_row03_traceSegment_015_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3408 17 17, g32p_row03_traceSegment_015_3408_0017, g32p_row03_traceSegment_015_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 3375 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3375 33 34, g32p_row03_traceSegment_015_3375_0033, g32p_row03_traceSegment_015_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3442 8 9, g32p_row03_traceSegment_015_3442_0008, g32p_row03_traceSegment_015_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3459 8 9, g32p_row03_traceSegment_015_3459_0008, g32p_row03_traceSegment_015_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3442 17 17, g32p_row03_traceSegment_015_3442_0017, g32p_row03_traceSegment_015_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3484 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3476 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3476 8 9, g32p_row03_traceSegment_015_3476_0008, g32p_row03_traceSegment_015_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3493 8 9, g32p_row03_traceSegment_015_3493_0008, g32p_row03_traceSegment_015_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3476 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3476 17 17, g32p_row03_traceSegment_015_3476_0017, g32p_row03_traceSegment_015_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 3442 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3442 34 34, g32p_row03_traceSegment_015_3442_0034, g32p_row03_traceSegment_015_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 3375 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3375 67 68, g32p_row03_traceSegment_015_3375_0067, g32p_row03_traceSegment_015_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 3240 270 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3240 135 135, g32p_row03_traceSegment_015_3240_0135, g32p_row03_traceSegment_015_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3526 8 9, g32p_row03_traceSegment_015_3526_0008, g32p_row03_traceSegment_015_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3510 16 17, g32p_row03_traceSegment_015_3510_0016, g32p_row03_traceSegment_015_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3551 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3543 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3543 8 9, g32p_row03_traceSegment_015_3543_0008, g32p_row03_traceSegment_015_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3560 8 9, g32p_row03_traceSegment_015_3560_0008, g32p_row03_traceSegment_015_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3543 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3543 17 17, g32p_row03_traceSegment_015_3543_0017, g32p_row03_traceSegment_015_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 3510 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3510 33 34, g32p_row03_traceSegment_015_3510_0033, g32p_row03_traceSegment_015_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3585 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3577 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3577 8 9, g32p_row03_traceSegment_015_3577_0008, g32p_row03_traceSegment_015_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3594 8 9, g32p_row03_traceSegment_015_3594_0008, g32p_row03_traceSegment_015_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3577 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3577 17 17, g32p_row03_traceSegment_015_3577_0017, g32p_row03_traceSegment_015_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3611 8 9, g32p_row03_traceSegment_015_3611_0008, g32p_row03_traceSegment_015_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3628 8 9, g32p_row03_traceSegment_015_3628_0008, g32p_row03_traceSegment_015_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3611 17 17, g32p_row03_traceSegment_015_3611_0017, g32p_row03_traceSegment_015_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 3577 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3577 34 34, g32p_row03_traceSegment_015_3577_0034, g32p_row03_traceSegment_015_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 3510 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3510 67 68, g32p_row03_traceSegment_015_3510_0067, g32p_row03_traceSegment_015_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3661 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3661 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3661 8 9, g32p_row03_traceSegment_015_3661_0008, g32p_row03_traceSegment_015_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 3645 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3645 16 17, g32p_row03_traceSegment_015_3645_0016, g32p_row03_traceSegment_015_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3686 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3678 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3678 8 9, g32p_row03_traceSegment_015_3678_0008, g32p_row03_traceSegment_015_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3695 8 9, g32p_row03_traceSegment_015_3695_0008, g32p_row03_traceSegment_015_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3678 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3678 17 17, g32p_row03_traceSegment_015_3678_0017, g32p_row03_traceSegment_015_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 3645 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3645 33 34, g32p_row03_traceSegment_015_3645_0033, g32p_row03_traceSegment_015_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3712 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3720 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3712 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3712 8 9, g32p_row03_traceSegment_015_3712_0008, g32p_row03_traceSegment_015_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3729 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3729 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3729 8 9, g32p_row03_traceSegment_015_3729_0008, g32p_row03_traceSegment_015_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3712 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3712 17 17, g32p_row03_traceSegment_015_3712_0017, g32p_row03_traceSegment_015_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3746 8 9, g32p_row03_traceSegment_015_3746_0008, g32p_row03_traceSegment_015_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3763 8 9, g32p_row03_traceSegment_015_3763_0008, g32p_row03_traceSegment_015_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3746 17 17, g32p_row03_traceSegment_015_3746_0017, g32p_row03_traceSegment_015_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 3712 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3712 34 34, g32p_row03_traceSegment_015_3712_0034, g32p_row03_traceSegment_015_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 3645 135 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3645 67 68, g32p_row03_traceSegment_015_3645_0067, g32p_row03_traceSegment_015_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 3510 270 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3510 135 135, g32p_row03_traceSegment_015_3510_0135, g32p_row03_traceSegment_015_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_015 3240 540 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3240 270 270, g32p_row03_traceSegment_015_3240_0270, g32p_row03_traceSegment_015_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3804 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3796 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3796 8 9, g32p_row03_traceSegment_015_3796_0008, g32p_row03_traceSegment_015_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 3780 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3780 16 17, g32p_row03_traceSegment_015_3780_0016, g32p_row03_traceSegment_015_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3813 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3813 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3813 8 9, g32p_row03_traceSegment_015_3813_0008, g32p_row03_traceSegment_015_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3830 8 9, g32p_row03_traceSegment_015_3830_0008, g32p_row03_traceSegment_015_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3813 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3813 17 17, g32p_row03_traceSegment_015_3813_0017, g32p_row03_traceSegment_015_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 3780 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3780 33 34, g32p_row03_traceSegment_015_3780_0033, g32p_row03_traceSegment_015_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3847 8 9, g32p_row03_traceSegment_015_3847_0008, g32p_row03_traceSegment_015_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3864 8 9, g32p_row03_traceSegment_015_3864_0008, g32p_row03_traceSegment_015_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3847 17 17, g32p_row03_traceSegment_015_3847_0017, g32p_row03_traceSegment_015_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3881 8 9, g32p_row03_traceSegment_015_3881_0008, g32p_row03_traceSegment_015_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3898 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3898 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3898 8 9, g32p_row03_traceSegment_015_3898_0008, g32p_row03_traceSegment_015_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3881 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3881 17 17, g32p_row03_traceSegment_015_3881_0017, g32p_row03_traceSegment_015_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 3847 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3847 34 34, g32p_row03_traceSegment_015_3847_0034, g32p_row03_traceSegment_015_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 3780 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3780 67 68, g32p_row03_traceSegment_015_3780_0067, g32p_row03_traceSegment_015_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3931 8 9, g32p_row03_traceSegment_015_3931_0008, g32p_row03_traceSegment_015_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3915 16 17, g32p_row03_traceSegment_015_3915_0016, g32p_row03_traceSegment_015_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3948 8 9, g32p_row03_traceSegment_015_3948_0008, g32p_row03_traceSegment_015_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3965 8 9, g32p_row03_traceSegment_015_3965_0008, g32p_row03_traceSegment_015_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3948 17 17, g32p_row03_traceSegment_015_3948_0017, g32p_row03_traceSegment_015_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3915 33 34, g32p_row03_traceSegment_015_3915_0033, g32p_row03_traceSegment_015_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3982 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3982 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3982 8 9, g32p_row03_traceSegment_015_3982_0008, g32p_row03_traceSegment_015_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 3999 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 3999 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3999 8 9, g32p_row03_traceSegment_015_3999_0008, g32p_row03_traceSegment_015_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 3982 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3982 17 17, g32p_row03_traceSegment_015_3982_0017, g32p_row03_traceSegment_015_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4016 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4016 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4016 8 9, g32p_row03_traceSegment_015_4016_0008, g32p_row03_traceSegment_015_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4033 8 9, g32p_row03_traceSegment_015_4033_0008, g32p_row03_traceSegment_015_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 4016 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4016 17 17, g32p_row03_traceSegment_015_4016_0017, g32p_row03_traceSegment_015_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 3982 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3982 34 34, g32p_row03_traceSegment_015_3982_0034, g32p_row03_traceSegment_015_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 3915 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3915 67 68, g32p_row03_traceSegment_015_3915_0067, g32p_row03_traceSegment_015_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 3780 270 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3780 135 135, g32p_row03_traceSegment_015_3780_0135, g32p_row03_traceSegment_015_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4066 8 9, g32p_row03_traceSegment_015_4066_0008, g32p_row03_traceSegment_015_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4050 16 17, g32p_row03_traceSegment_015_4050_0016, g32p_row03_traceSegment_015_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4083 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4083 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4083 8 9, g32p_row03_traceSegment_015_4083_0008, g32p_row03_traceSegment_015_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4108 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4100 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4100 8 9, g32p_row03_traceSegment_015_4100_0008, g32p_row03_traceSegment_015_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 4083 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4083 17 17, g32p_row03_traceSegment_015_4083_0017, g32p_row03_traceSegment_015_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 4050 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4050 33 34, g32p_row03_traceSegment_015_4050_0033, g32p_row03_traceSegment_015_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4117 8 9, g32p_row03_traceSegment_015_4117_0008, g32p_row03_traceSegment_015_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4134 8 9, g32p_row03_traceSegment_015_4134_0008, g32p_row03_traceSegment_015_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4117 17 17, g32p_row03_traceSegment_015_4117_0017, g32p_row03_traceSegment_015_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4151 8 9, g32p_row03_traceSegment_015_4151_0008, g32p_row03_traceSegment_015_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4168 8 9, g32p_row03_traceSegment_015_4168_0008, g32p_row03_traceSegment_015_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4151 17 17, g32p_row03_traceSegment_015_4151_0017, g32p_row03_traceSegment_015_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4117 34 34, g32p_row03_traceSegment_015_4117_0034, g32p_row03_traceSegment_015_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 4050 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4050 67 68, g32p_row03_traceSegment_015_4050_0067, g32p_row03_traceSegment_015_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_015 4185 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4201 8 9, g32p_row03_traceSegment_015_4201_0008, g32p_row03_traceSegment_015_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_015 4185 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4185 16 17, g32p_row03_traceSegment_015_4185_0016, g32p_row03_traceSegment_015_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4218 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4218 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4218 8 9, g32p_row03_traceSegment_015_4218_0008, g32p_row03_traceSegment_015_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4235 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4235 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4235 8 9, g32p_row03_traceSegment_015_4235_0008, g32p_row03_traceSegment_015_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 4218 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4218 17 17, g32p_row03_traceSegment_015_4218_0017, g32p_row03_traceSegment_015_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_015 4185 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4185 33 34, g32p_row03_traceSegment_015_4185_0033, g32p_row03_traceSegment_015_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4252 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4260 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4252 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4252 8 9, g32p_row03_traceSegment_015_4252_0008, g32p_row03_traceSegment_015_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4269 8 9, g32p_row03_traceSegment_015_4269_0008, g32p_row03_traceSegment_015_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 4252 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4252 17 17, g32p_row03_traceSegment_015_4252_0017, g32p_row03_traceSegment_015_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4286 8 9, g32p_row03_traceSegment_015_4286_0008, g32p_row03_traceSegment_015_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_015 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_015 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_015_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_015 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4303 8 9, g32p_row03_traceSegment_015_4303_0008, g32p_row03_traceSegment_015_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_015 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4286 17 17, g32p_row03_traceSegment_015_4286_0017, g32p_row03_traceSegment_015_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_015 4252 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4252 34 34, g32p_row03_traceSegment_015_4252_0034, g32p_row03_traceSegment_015_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_015 4185 135 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4185 67 68, g32p_row03_traceSegment_015_4185_0067, g32p_row03_traceSegment_015_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_015_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_015 4050 270 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 4050 135 135, g32p_row03_traceSegment_015_4050_0135, g32p_row03_traceSegment_015_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_015 3780 540 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3780 270 270, g32p_row03_traceSegment_015_3780_0270, g32p_row03_traceSegment_015_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_015_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_015 3240 1080 = [0, 27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 3240 540 540, g32p_row03_traceSegment_015_3240_0540, g32p_row03_traceSegment_015_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_015_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_015 2160 2160 = [0, 65] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 2160 1080 1080, g32p_row03_traceSegment_015_2160_1080, g32p_row03_traceSegment_015_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_015_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_015 0 4320 = [0, 120] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_015 0 2160 2160, g32p_row03_traceSegment_015_0000_2160, g32p_row03_traceSegment_015_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 15 = [0, 120] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_015_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_016 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 16 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_016_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 16 8 9, g32p_row03_traceSegment_016_0016_0008, g32p_row03_traceSegment_016_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 0 16 17, g32p_row03_traceSegment_016_0000_0016, g32p_row03_traceSegment_016_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 33 8 9, g32p_row03_traceSegment_016_0033_0008, g32p_row03_traceSegment_016_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 50 8 9, g32p_row03_traceSegment_016_0050_0008, g32p_row03_traceSegment_016_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 33 17 17, g32p_row03_traceSegment_016_0033_0017, g32p_row03_traceSegment_016_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 0 33 34, g32p_row03_traceSegment_016_0000_0033, g32p_row03_traceSegment_016_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 67 8 9, g32p_row03_traceSegment_016_0067_0008, g32p_row03_traceSegment_016_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 84 8 9, g32p_row03_traceSegment_016_0084_0008, g32p_row03_traceSegment_016_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 67 17 17, g32p_row03_traceSegment_016_0067_0017, g32p_row03_traceSegment_016_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 101 8 9, g32p_row03_traceSegment_016_0101_0008, g32p_row03_traceSegment_016_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 118 8 9, g32p_row03_traceSegment_016_0118_0008, g32p_row03_traceSegment_016_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 101 17 17, g32p_row03_traceSegment_016_0101_0017, g32p_row03_traceSegment_016_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 67 34 34, g32p_row03_traceSegment_016_0067_0034, g32p_row03_traceSegment_016_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 0 67 68, g32p_row03_traceSegment_016_0000_0067, g32p_row03_traceSegment_016_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 151 8 9, g32p_row03_traceSegment_016_0151_0008, g32p_row03_traceSegment_016_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 135 16 17, g32p_row03_traceSegment_016_0135_0016, g32p_row03_traceSegment_016_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 168 8 9, g32p_row03_traceSegment_016_0168_0008, g32p_row03_traceSegment_016_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 185 8 9, g32p_row03_traceSegment_016_0185_0008, g32p_row03_traceSegment_016_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 168 17 17, g32p_row03_traceSegment_016_0168_0017, g32p_row03_traceSegment_016_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 135 33 34, g32p_row03_traceSegment_016_0135_0033, g32p_row03_traceSegment_016_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 202 8 9, g32p_row03_traceSegment_016_0202_0008, g32p_row03_traceSegment_016_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 219 8 9, g32p_row03_traceSegment_016_0219_0008, g32p_row03_traceSegment_016_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 202 17 17, g32p_row03_traceSegment_016_0202_0017, g32p_row03_traceSegment_016_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 236 8 9, g32p_row03_traceSegment_016_0236_0008, g32p_row03_traceSegment_016_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 253 8 9, g32p_row03_traceSegment_016_0253_0008, g32p_row03_traceSegment_016_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 236 17 17, g32p_row03_traceSegment_016_0236_0017, g32p_row03_traceSegment_016_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 202 34 34, g32p_row03_traceSegment_016_0202_0034, g32p_row03_traceSegment_016_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 135 67 68, g32p_row03_traceSegment_016_0135_0067, g32p_row03_traceSegment_016_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 0 135 135, g32p_row03_traceSegment_016_0000_0135, g32p_row03_traceSegment_016_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 286 8 9, g32p_row03_traceSegment_016_0286_0008, g32p_row03_traceSegment_016_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 270 16 17, g32p_row03_traceSegment_016_0270_0016, g32p_row03_traceSegment_016_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 303 8 9, g32p_row03_traceSegment_016_0303_0008, g32p_row03_traceSegment_016_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 320 8 9, g32p_row03_traceSegment_016_0320_0008, g32p_row03_traceSegment_016_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 303 17 17, g32p_row03_traceSegment_016_0303_0017, g32p_row03_traceSegment_016_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 270 33 34, g32p_row03_traceSegment_016_0270_0033, g32p_row03_traceSegment_016_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 337 8 9, g32p_row03_traceSegment_016_0337_0008, g32p_row03_traceSegment_016_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 354 8 9, g32p_row03_traceSegment_016_0354_0008, g32p_row03_traceSegment_016_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 337 17 17, g32p_row03_traceSegment_016_0337_0017, g32p_row03_traceSegment_016_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 371 8 9, g32p_row03_traceSegment_016_0371_0008, g32p_row03_traceSegment_016_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 388 8 9, g32p_row03_traceSegment_016_0388_0008, g32p_row03_traceSegment_016_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 371 17 17, g32p_row03_traceSegment_016_0371_0017, g32p_row03_traceSegment_016_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 337 34 34, g32p_row03_traceSegment_016_0337_0034, g32p_row03_traceSegment_016_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 270 67 68, g32p_row03_traceSegment_016_0270_0067, g32p_row03_traceSegment_016_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 421 8 9, g32p_row03_traceSegment_016_0421_0008, g32p_row03_traceSegment_016_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 405 16 17, g32p_row03_traceSegment_016_0405_0016, g32p_row03_traceSegment_016_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 446 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 438 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 438 8 9, g32p_row03_traceSegment_016_0438_0008, g32p_row03_traceSegment_016_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 463 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 455 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 455 8 9, g32p_row03_traceSegment_016_0455_0008, g32p_row03_traceSegment_016_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 438 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 438 17 17, g32p_row03_traceSegment_016_0438_0017, g32p_row03_traceSegment_016_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 405 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 405 33 34, g32p_row03_traceSegment_016_0405_0033, g32p_row03_traceSegment_016_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 472 8 9, g32p_row03_traceSegment_016_0472_0008, g32p_row03_traceSegment_016_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 489 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 489 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 489 8 9, g32p_row03_traceSegment_016_0489_0008, g32p_row03_traceSegment_016_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 472 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 472 17 17, g32p_row03_traceSegment_016_0472_0017, g32p_row03_traceSegment_016_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 506 8 9, g32p_row03_traceSegment_016_0506_0008, g32p_row03_traceSegment_016_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 523 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 531 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 523 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 523 8 9, g32p_row03_traceSegment_016_0523_0008, g32p_row03_traceSegment_016_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 506 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 506 17 17, g32p_row03_traceSegment_016_0506_0017, g32p_row03_traceSegment_016_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 472 68 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 472 34 34, g32p_row03_traceSegment_016_0472_0034, g32p_row03_traceSegment_016_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 405 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 405 67 68, g32p_row03_traceSegment_016_0405_0067, g32p_row03_traceSegment_016_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 270 270 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 270 135 135, g32p_row03_traceSegment_016_0270_0135, g32p_row03_traceSegment_016_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_016 0 540 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 0 270 270, g32p_row03_traceSegment_016_0000_0270, g32p_row03_traceSegment_016_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 540 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 564 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 556 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 556 8 9, g32p_row03_traceSegment_016_0556_0008, g32p_row03_traceSegment_016_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 540 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 540 16 17, g32p_row03_traceSegment_016_0540_0016, g32p_row03_traceSegment_016_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 573 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 573 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 573 8 9, g32p_row03_traceSegment_016_0573_0008, g32p_row03_traceSegment_016_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 590 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 590 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 590 8 9, g32p_row03_traceSegment_016_0590_0008, g32p_row03_traceSegment_016_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 573 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 573 17 17, g32p_row03_traceSegment_016_0573_0017, g32p_row03_traceSegment_016_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 540 67 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 540 33 34, g32p_row03_traceSegment_016_0540_0033, g32p_row03_traceSegment_016_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 607 8 9, g32p_row03_traceSegment_016_0607_0008, g32p_row03_traceSegment_016_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 624 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 632 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 624 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 624 8 9, g32p_row03_traceSegment_016_0624_0008, g32p_row03_traceSegment_016_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 607 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 607 17 17, g32p_row03_traceSegment_016_0607_0017, g32p_row03_traceSegment_016_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 641 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 641 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 641 8 9, g32p_row03_traceSegment_016_0641_0008, g32p_row03_traceSegment_016_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 658 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 658 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 658 8 9, g32p_row03_traceSegment_016_0658_0008, g32p_row03_traceSegment_016_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 641 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 641 17 17, g32p_row03_traceSegment_016_0641_0017, g32p_row03_traceSegment_016_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 607 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 607 34 34, g32p_row03_traceSegment_016_0607_0034, g32p_row03_traceSegment_016_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 540 135 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 540 67 68, g32p_row03_traceSegment_016_0540_0067, g32p_row03_traceSegment_016_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 675 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 699 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 691 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 691 8 9, g32p_row03_traceSegment_016_0691_0008, g32p_row03_traceSegment_016_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 675 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 675 16 17, g32p_row03_traceSegment_016_0675_0016, g32p_row03_traceSegment_016_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 708 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 708 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 708 8 9, g32p_row03_traceSegment_016_0708_0008, g32p_row03_traceSegment_016_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 725 8 9, g32p_row03_traceSegment_016_0725_0008, g32p_row03_traceSegment_016_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 708 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 708 17 17, g32p_row03_traceSegment_016_0708_0017, g32p_row03_traceSegment_016_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 675 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 675 33 34, g32p_row03_traceSegment_016_0675_0033, g32p_row03_traceSegment_016_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 742 8 9, g32p_row03_traceSegment_016_0742_0008, g32p_row03_traceSegment_016_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 759 8 9, g32p_row03_traceSegment_016_0759_0008, g32p_row03_traceSegment_016_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 742 17 17, g32p_row03_traceSegment_016_0742_0017, g32p_row03_traceSegment_016_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 776 8 9, g32p_row03_traceSegment_016_0776_0008, g32p_row03_traceSegment_016_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 793 8 9, g32p_row03_traceSegment_016_0793_0008, g32p_row03_traceSegment_016_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 776 17 17, g32p_row03_traceSegment_016_0776_0017, g32p_row03_traceSegment_016_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 742 34 34, g32p_row03_traceSegment_016_0742_0034, g32p_row03_traceSegment_016_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 675 135 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 675 67 68, g32p_row03_traceSegment_016_0675_0067, g32p_row03_traceSegment_016_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 540 270 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 540 135 135, g32p_row03_traceSegment_016_0540_0135, g32p_row03_traceSegment_016_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 826 8 9, g32p_row03_traceSegment_016_0826_0008, g32p_row03_traceSegment_016_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 810 16 17, g32p_row03_traceSegment_016_0810_0016, g32p_row03_traceSegment_016_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 843 8 9, g32p_row03_traceSegment_016_0843_0008, g32p_row03_traceSegment_016_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 860 8 9, g32p_row03_traceSegment_016_0860_0008, g32p_row03_traceSegment_016_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 843 17 17, g32p_row03_traceSegment_016_0843_0017, g32p_row03_traceSegment_016_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 810 33 34, g32p_row03_traceSegment_016_0810_0033, g32p_row03_traceSegment_016_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 877 8 9, g32p_row03_traceSegment_016_0877_0008, g32p_row03_traceSegment_016_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 894 8 9, g32p_row03_traceSegment_016_0894_0008, g32p_row03_traceSegment_016_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 877 17 17, g32p_row03_traceSegment_016_0877_0017, g32p_row03_traceSegment_016_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 911 8 9, g32p_row03_traceSegment_016_0911_0008, g32p_row03_traceSegment_016_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 928 8 9, g32p_row03_traceSegment_016_0928_0008, g32p_row03_traceSegment_016_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 911 17 17, g32p_row03_traceSegment_016_0911_0017, g32p_row03_traceSegment_016_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 877 34 34, g32p_row03_traceSegment_016_0877_0034, g32p_row03_traceSegment_016_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 810 67 68, g32p_row03_traceSegment_016_0810_0067, g32p_row03_traceSegment_016_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 961 8 9, g32p_row03_traceSegment_016_0961_0008, g32p_row03_traceSegment_016_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 945 16 17, g32p_row03_traceSegment_016_0945_0016, g32p_row03_traceSegment_016_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 978 8 9, g32p_row03_traceSegment_016_0978_0008, g32p_row03_traceSegment_016_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 995 8 9, g32p_row03_traceSegment_016_0995_0008, g32p_row03_traceSegment_016_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 978 17 17, g32p_row03_traceSegment_016_0978_0017, g32p_row03_traceSegment_016_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 945 33 34, g32p_row03_traceSegment_016_0945_0033, g32p_row03_traceSegment_016_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1012 8 9, g32p_row03_traceSegment_016_1012_0008, g32p_row03_traceSegment_016_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1029 8 9, g32p_row03_traceSegment_016_1029_0008, g32p_row03_traceSegment_016_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1012 17 17, g32p_row03_traceSegment_016_1012_0017, g32p_row03_traceSegment_016_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1046 8 9, g32p_row03_traceSegment_016_1046_0008, g32p_row03_traceSegment_016_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1063 8 9, g32p_row03_traceSegment_016_1063_0008, g32p_row03_traceSegment_016_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1046 17 17, g32p_row03_traceSegment_016_1046_0017, g32p_row03_traceSegment_016_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1012 34 34, g32p_row03_traceSegment_016_1012_0034, g32p_row03_traceSegment_016_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 945 67 68, g32p_row03_traceSegment_016_0945_0067, g32p_row03_traceSegment_016_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 810 135 135, g32p_row03_traceSegment_016_0810_0135, g32p_row03_traceSegment_016_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_016 540 540 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 540 270 270, g32p_row03_traceSegment_016_0540_0270, g32p_row03_traceSegment_016_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_016 0 1080 = [0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 0 540 540, g32p_row03_traceSegment_016_0000_0540, g32p_row03_traceSegment_016_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1096 8 9, g32p_row03_traceSegment_016_1096_0008, g32p_row03_traceSegment_016_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1080 16 17, g32p_row03_traceSegment_016_1080_0016, g32p_row03_traceSegment_016_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1113 8 9, g32p_row03_traceSegment_016_1113_0008, g32p_row03_traceSegment_016_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1130 8 9, g32p_row03_traceSegment_016_1130_0008, g32p_row03_traceSegment_016_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1113 17 17, g32p_row03_traceSegment_016_1113_0017, g32p_row03_traceSegment_016_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1080 33 34, g32p_row03_traceSegment_016_1080_0033, g32p_row03_traceSegment_016_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1147 8 9, g32p_row03_traceSegment_016_1147_0008, g32p_row03_traceSegment_016_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1164 8 9, g32p_row03_traceSegment_016_1164_0008, g32p_row03_traceSegment_016_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1147 17 17, g32p_row03_traceSegment_016_1147_0017, g32p_row03_traceSegment_016_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1181 8 9, g32p_row03_traceSegment_016_1181_0008, g32p_row03_traceSegment_016_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1198 8 9, g32p_row03_traceSegment_016_1198_0008, g32p_row03_traceSegment_016_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1181 17 17, g32p_row03_traceSegment_016_1181_0017, g32p_row03_traceSegment_016_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1147 34 34, g32p_row03_traceSegment_016_1147_0034, g32p_row03_traceSegment_016_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1080 67 68, g32p_row03_traceSegment_016_1080_0067, g32p_row03_traceSegment_016_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1231 8 9, g32p_row03_traceSegment_016_1231_0008, g32p_row03_traceSegment_016_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1215 16 17, g32p_row03_traceSegment_016_1215_0016, g32p_row03_traceSegment_016_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1248 8 9, g32p_row03_traceSegment_016_1248_0008, g32p_row03_traceSegment_016_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1265 8 9, g32p_row03_traceSegment_016_1265_0008, g32p_row03_traceSegment_016_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1248 17 17, g32p_row03_traceSegment_016_1248_0017, g32p_row03_traceSegment_016_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1215 33 34, g32p_row03_traceSegment_016_1215_0033, g32p_row03_traceSegment_016_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1282 8 9, g32p_row03_traceSegment_016_1282_0008, g32p_row03_traceSegment_016_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1299 8 9, g32p_row03_traceSegment_016_1299_0008, g32p_row03_traceSegment_016_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1282 17 17, g32p_row03_traceSegment_016_1282_0017, g32p_row03_traceSegment_016_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1316 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1316 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1316 8 9, g32p_row03_traceSegment_016_1316_0008, g32p_row03_traceSegment_016_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1333 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1333 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1333 8 9, g32p_row03_traceSegment_016_1333_0008, g32p_row03_traceSegment_016_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1316 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1316 17 17, g32p_row03_traceSegment_016_1316_0017, g32p_row03_traceSegment_016_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 1282 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1282 34 34, g32p_row03_traceSegment_016_1282_0034, g32p_row03_traceSegment_016_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 1215 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1215 67 68, g32p_row03_traceSegment_016_1215_0067, g32p_row03_traceSegment_016_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 1080 270 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1080 135 135, g32p_row03_traceSegment_016_1080_0135, g32p_row03_traceSegment_016_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 1350 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1366 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1366 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1366 8 9, g32p_row03_traceSegment_016_1366_0008, g32p_row03_traceSegment_016_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 1350 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1350 16 17, g32p_row03_traceSegment_016_1350_0016, g32p_row03_traceSegment_016_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1383 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1391 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1383 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1383 8 9, g32p_row03_traceSegment_016_1383_0008, g32p_row03_traceSegment_016_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1400 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1400 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1400 8 9, g32p_row03_traceSegment_016_1400_0008, g32p_row03_traceSegment_016_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1383 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1383 17 17, g32p_row03_traceSegment_016_1383_0017, g32p_row03_traceSegment_016_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 1350 67 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1350 33 34, g32p_row03_traceSegment_016_1350_0033, g32p_row03_traceSegment_016_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1417 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1425 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1417 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1417 8 9, g32p_row03_traceSegment_016_1417_0008, g32p_row03_traceSegment_016_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1434 8 9, g32p_row03_traceSegment_016_1434_0008, g32p_row03_traceSegment_016_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1417 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1417 17 17, g32p_row03_traceSegment_016_1417_0017, g32p_row03_traceSegment_016_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1451 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1451 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1451 8 9, g32p_row03_traceSegment_016_1451_0008, g32p_row03_traceSegment_016_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1468 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1468 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1468 8 9, g32p_row03_traceSegment_016_1468_0008, g32p_row03_traceSegment_016_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1451 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1451 17 17, g32p_row03_traceSegment_016_1451_0017, g32p_row03_traceSegment_016_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 1417 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1417 34 34, g32p_row03_traceSegment_016_1417_0034, g32p_row03_traceSegment_016_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 1350 135 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1350 67 68, g32p_row03_traceSegment_016_1350_0067, g32p_row03_traceSegment_016_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1501 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1509 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1501 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1501 8 9, g32p_row03_traceSegment_016_1501_0008, g32p_row03_traceSegment_016_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 1485 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1485 16 17, g32p_row03_traceSegment_016_1485_0016, g32p_row03_traceSegment_016_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1518 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1526 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1518 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1518 8 9, g32p_row03_traceSegment_016_1518_0008, g32p_row03_traceSegment_016_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1543 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1535 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1535 8 9, g32p_row03_traceSegment_016_1535_0008, g32p_row03_traceSegment_016_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1518 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1518 17 17, g32p_row03_traceSegment_016_1518_0017, g32p_row03_traceSegment_016_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 1485 67 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1485 33 34, g32p_row03_traceSegment_016_1485_0033, g32p_row03_traceSegment_016_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1552 8 9, g32p_row03_traceSegment_016_1552_0008, g32p_row03_traceSegment_016_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1569 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1577 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1569 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1569 8 9, g32p_row03_traceSegment_016_1569_0008, g32p_row03_traceSegment_016_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1552 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1552 17 17, g32p_row03_traceSegment_016_1552_0017, g32p_row03_traceSegment_016_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1586 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1586 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1586 8 9, g32p_row03_traceSegment_016_1586_0008, g32p_row03_traceSegment_016_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1603 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1611 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1603 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1603 8 9, g32p_row03_traceSegment_016_1603_0008, g32p_row03_traceSegment_016_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1586 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1586 17 17, g32p_row03_traceSegment_016_1586_0017, g32p_row03_traceSegment_016_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 1552 68 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1552 34 34, g32p_row03_traceSegment_016_1552_0034, g32p_row03_traceSegment_016_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 1485 135 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1485 67 68, g32p_row03_traceSegment_016_1485_0067, g32p_row03_traceSegment_016_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 1350 270 = [0, 0, 0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1350 135 135, g32p_row03_traceSegment_016_1350_0135, g32p_row03_traceSegment_016_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_016 1080 540 = [0, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1080 270 270, g32p_row03_traceSegment_016_1080_0270, g32p_row03_traceSegment_016_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 1620 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1636 8 9, g32p_row03_traceSegment_016_1636_0008, g32p_row03_traceSegment_016_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 1620 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1620 16 17, g32p_row03_traceSegment_016_1620_0016, g32p_row03_traceSegment_016_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1653 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1653 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1653 8 9, g32p_row03_traceSegment_016_1653_0008, g32p_row03_traceSegment_016_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1678 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1670 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1670 8 9, g32p_row03_traceSegment_016_1670_0008, g32p_row03_traceSegment_016_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1653 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1653 17 17, g32p_row03_traceSegment_016_1653_0017, g32p_row03_traceSegment_016_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 1620 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1620 33 34, g32p_row03_traceSegment_016_1620_0033, g32p_row03_traceSegment_016_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1687 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1695 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1687 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1687 8 9, g32p_row03_traceSegment_016_1687_0008, g32p_row03_traceSegment_016_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1704 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1712 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1704 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1704 8 9, g32p_row03_traceSegment_016_1704_0008, g32p_row03_traceSegment_016_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1687 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1687 17 17, g32p_row03_traceSegment_016_1687_0017, g32p_row03_traceSegment_016_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1721 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1729 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1721 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1721 8 9, g32p_row03_traceSegment_016_1721_0008, g32p_row03_traceSegment_016_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1738 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1738 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1738 8 9, g32p_row03_traceSegment_016_1738_0008, g32p_row03_traceSegment_016_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1721 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1721 17 17, g32p_row03_traceSegment_016_1721_0017, g32p_row03_traceSegment_016_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 1687 68 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1687 34 34, g32p_row03_traceSegment_016_1687_0034, g32p_row03_traceSegment_016_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 1620 135 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1620 67 68, g32p_row03_traceSegment_016_1620_0067, g32p_row03_traceSegment_016_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 1755 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1771 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1771 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1771 8 9, g32p_row03_traceSegment_016_1771_0008, g32p_row03_traceSegment_016_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 1755 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1755 16 17, g32p_row03_traceSegment_016_1755_0016, g32p_row03_traceSegment_016_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1788 8 9, g32p_row03_traceSegment_016_1788_0008, g32p_row03_traceSegment_016_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1805 8 9, g32p_row03_traceSegment_016_1805_0008, g32p_row03_traceSegment_016_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1788 17 17, g32p_row03_traceSegment_016_1788_0017, g32p_row03_traceSegment_016_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 1755 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1755 33 34, g32p_row03_traceSegment_016_1755_0033, g32p_row03_traceSegment_016_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1822 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1822 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1822 8 9, g32p_row03_traceSegment_016_1822_0008, g32p_row03_traceSegment_016_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1847 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1839 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1839 8 9, g32p_row03_traceSegment_016_1839_0008, g32p_row03_traceSegment_016_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1822 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1822 17 17, g32p_row03_traceSegment_016_1822_0017, g32p_row03_traceSegment_016_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1856 8 9, g32p_row03_traceSegment_016_1856_0008, g32p_row03_traceSegment_016_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1873 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1881 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1873 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1873 8 9, g32p_row03_traceSegment_016_1873_0008, g32p_row03_traceSegment_016_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1856 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1856 17 17, g32p_row03_traceSegment_016_1856_0017, g32p_row03_traceSegment_016_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 1822 68 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1822 34 34, g32p_row03_traceSegment_016_1822_0034, g32p_row03_traceSegment_016_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 1755 135 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1755 67 68, g32p_row03_traceSegment_016_1755_0067, g32p_row03_traceSegment_016_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 1620 270 = [0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1620 135 135, g32p_row03_traceSegment_016_1620_0135, g32p_row03_traceSegment_016_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 1890 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1906 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1914 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1906 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1906 8 9, g32p_row03_traceSegment_016_1906_0008, g32p_row03_traceSegment_016_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 1890 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1890 16 17, g32p_row03_traceSegment_016_1890_0016, g32p_row03_traceSegment_016_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1923 8 9, g32p_row03_traceSegment_016_1923_0008, g32p_row03_traceSegment_016_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1948 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1940 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1940 8 9, g32p_row03_traceSegment_016_1940_0008, g32p_row03_traceSegment_016_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1923 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1923 17 17, g32p_row03_traceSegment_016_1923_0017, g32p_row03_traceSegment_016_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 1890 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1890 33 34, g32p_row03_traceSegment_016_1890_0033, g32p_row03_traceSegment_016_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1965 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1957 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1957 8 9, g32p_row03_traceSegment_016_1957_0008, g32p_row03_traceSegment_016_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1974 8 9, g32p_row03_traceSegment_016_1974_0008, g32p_row03_traceSegment_016_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1957 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1957 17 17, g32p_row03_traceSegment_016_1957_0017, g32p_row03_traceSegment_016_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1991 8 9, g32p_row03_traceSegment_016_1991_0008, g32p_row03_traceSegment_016_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2008 8 9, g32p_row03_traceSegment_016_2008_0008, g32p_row03_traceSegment_016_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1991 17 17, g32p_row03_traceSegment_016_1991_0017, g32p_row03_traceSegment_016_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 1957 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1957 34 34, g32p_row03_traceSegment_016_1957_0034, g32p_row03_traceSegment_016_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 1890 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1890 67 68, g32p_row03_traceSegment_016_1890_0067, g32p_row03_traceSegment_016_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2041 8 9, g32p_row03_traceSegment_016_2041_0008, g32p_row03_traceSegment_016_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2025 16 17, g32p_row03_traceSegment_016_2025_0016, g32p_row03_traceSegment_016_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2058 8 9, g32p_row03_traceSegment_016_2058_0008, g32p_row03_traceSegment_016_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2075 8 9, g32p_row03_traceSegment_016_2075_0008, g32p_row03_traceSegment_016_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2058 17 17, g32p_row03_traceSegment_016_2058_0017, g32p_row03_traceSegment_016_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2025 33 34, g32p_row03_traceSegment_016_2025_0033, g32p_row03_traceSegment_016_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2092 8 9, g32p_row03_traceSegment_016_2092_0008, g32p_row03_traceSegment_016_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2109 8 9, g32p_row03_traceSegment_016_2109_0008, g32p_row03_traceSegment_016_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2092 17 17, g32p_row03_traceSegment_016_2092_0017, g32p_row03_traceSegment_016_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2126 8 9, g32p_row03_traceSegment_016_2126_0008, g32p_row03_traceSegment_016_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2143 8 9, g32p_row03_traceSegment_016_2143_0008, g32p_row03_traceSegment_016_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2126 17 17, g32p_row03_traceSegment_016_2126_0017, g32p_row03_traceSegment_016_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2092 34 34, g32p_row03_traceSegment_016_2092_0034, g32p_row03_traceSegment_016_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2025 67 68, g32p_row03_traceSegment_016_2025_0067, g32p_row03_traceSegment_016_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 1890 270 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1890 135 135, g32p_row03_traceSegment_016_1890_0135, g32p_row03_traceSegment_016_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_016 1620 540 = [0, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1620 270 270, g32p_row03_traceSegment_016_1620_0270, g32p_row03_traceSegment_016_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_016_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_016 1080 1080 = [0, 0, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 1080 540 540, g32p_row03_traceSegment_016_1080_0540, g32p_row03_traceSegment_016_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_016 0 2160 = [0, 0, 0, 0, 66] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 0 1080 1080, g32p_row03_traceSegment_016_0000_1080, g32p_row03_traceSegment_016_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2176 8 9, g32p_row03_traceSegment_016_2176_0008, g32p_row03_traceSegment_016_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2160 16 17, g32p_row03_traceSegment_016_2160_0016, g32p_row03_traceSegment_016_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2193 8 9, g32p_row03_traceSegment_016_2193_0008, g32p_row03_traceSegment_016_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2210 8 9, g32p_row03_traceSegment_016_2210_0008, g32p_row03_traceSegment_016_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2193 17 17, g32p_row03_traceSegment_016_2193_0017, g32p_row03_traceSegment_016_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2160 33 34, g32p_row03_traceSegment_016_2160_0033, g32p_row03_traceSegment_016_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2227 8 9, g32p_row03_traceSegment_016_2227_0008, g32p_row03_traceSegment_016_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2244 8 9, g32p_row03_traceSegment_016_2244_0008, g32p_row03_traceSegment_016_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2227 17 17, g32p_row03_traceSegment_016_2227_0017, g32p_row03_traceSegment_016_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2261 8 9, g32p_row03_traceSegment_016_2261_0008, g32p_row03_traceSegment_016_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2286 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2278 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2278 8 9, g32p_row03_traceSegment_016_2278_0008, g32p_row03_traceSegment_016_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2261 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2261 17 17, g32p_row03_traceSegment_016_2261_0017, g32p_row03_traceSegment_016_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 2227 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2227 34 34, g32p_row03_traceSegment_016_2227_0034, g32p_row03_traceSegment_016_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 2160 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2160 67 68, g32p_row03_traceSegment_016_2160_0067, g32p_row03_traceSegment_016_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 2295 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2311 8 9, g32p_row03_traceSegment_016_2311_0008, g32p_row03_traceSegment_016_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 2295 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2295 16 17, g32p_row03_traceSegment_016_2295_0016, g32p_row03_traceSegment_016_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2328 8 9, g32p_row03_traceSegment_016_2328_0008, g32p_row03_traceSegment_016_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2345 8 9, g32p_row03_traceSegment_016_2345_0008, g32p_row03_traceSegment_016_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2328 17 17, g32p_row03_traceSegment_016_2328_0017, g32p_row03_traceSegment_016_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 2295 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2295 33 34, g32p_row03_traceSegment_016_2295_0033, g32p_row03_traceSegment_016_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2362 8 9, g32p_row03_traceSegment_016_2362_0008, g32p_row03_traceSegment_016_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2379 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2379 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2379 8 9, g32p_row03_traceSegment_016_2379_0008, g32p_row03_traceSegment_016_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2362 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2362 17 17, g32p_row03_traceSegment_016_2362_0017, g32p_row03_traceSegment_016_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2396 8 9, g32p_row03_traceSegment_016_2396_0008, g32p_row03_traceSegment_016_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2421 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2413 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2413 8 9, g32p_row03_traceSegment_016_2413_0008, g32p_row03_traceSegment_016_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2396 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2396 17 17, g32p_row03_traceSegment_016_2396_0017, g32p_row03_traceSegment_016_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 2362 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2362 34 34, g32p_row03_traceSegment_016_2362_0034, g32p_row03_traceSegment_016_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 2295 135 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2295 67 68, g32p_row03_traceSegment_016_2295_0067, g32p_row03_traceSegment_016_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 2160 270 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2160 135 135, g32p_row03_traceSegment_016_2160_0135, g32p_row03_traceSegment_016_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2446 8 9, g32p_row03_traceSegment_016_2446_0008, g32p_row03_traceSegment_016_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2430 16 17, g32p_row03_traceSegment_016_2430_0016, g32p_row03_traceSegment_016_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2471 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2463 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2463 8 9, g32p_row03_traceSegment_016_2463_0008, g32p_row03_traceSegment_016_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2480 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2480 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2480 8 9, g32p_row03_traceSegment_016_2480_0008, g32p_row03_traceSegment_016_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2463 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2463 17 17, g32p_row03_traceSegment_016_2463_0017, g32p_row03_traceSegment_016_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 2430 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2430 33 34, g32p_row03_traceSegment_016_2430_0033, g32p_row03_traceSegment_016_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2505 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2497 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2497 8 9, g32p_row03_traceSegment_016_2497_0008, g32p_row03_traceSegment_016_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2522 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2514 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2514 8 9, g32p_row03_traceSegment_016_2514_0008, g32p_row03_traceSegment_016_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2497 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2497 17 17, g32p_row03_traceSegment_016_2497_0017, g32p_row03_traceSegment_016_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2531 8 9, g32p_row03_traceSegment_016_2531_0008, g32p_row03_traceSegment_016_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2548 8 9, g32p_row03_traceSegment_016_2548_0008, g32p_row03_traceSegment_016_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2531 17 17, g32p_row03_traceSegment_016_2531_0017, g32p_row03_traceSegment_016_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 2497 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2497 34 34, g32p_row03_traceSegment_016_2497_0034, g32p_row03_traceSegment_016_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 2430 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2430 67 68, g32p_row03_traceSegment_016_2430_0067, g32p_row03_traceSegment_016_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2581 8 9, g32p_row03_traceSegment_016_2581_0008, g32p_row03_traceSegment_016_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2565 16 17, g32p_row03_traceSegment_016_2565_0016, g32p_row03_traceSegment_016_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2598 8 9, g32p_row03_traceSegment_016_2598_0008, g32p_row03_traceSegment_016_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2615 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2615 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2615 8 9, g32p_row03_traceSegment_016_2615_0008, g32p_row03_traceSegment_016_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2598 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2598 17 17, g32p_row03_traceSegment_016_2598_0017, g32p_row03_traceSegment_016_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 2565 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2565 33 34, g32p_row03_traceSegment_016_2565_0033, g32p_row03_traceSegment_016_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2640 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2632 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2632 8 9, g32p_row03_traceSegment_016_2632_0008, g32p_row03_traceSegment_016_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2649 8 9, g32p_row03_traceSegment_016_2649_0008, g32p_row03_traceSegment_016_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2632 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2632 17 17, g32p_row03_traceSegment_016_2632_0017, g32p_row03_traceSegment_016_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2666 8 9, g32p_row03_traceSegment_016_2666_0008, g32p_row03_traceSegment_016_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2683 8 9, g32p_row03_traceSegment_016_2683_0008, g32p_row03_traceSegment_016_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2666 17 17, g32p_row03_traceSegment_016_2666_0017, g32p_row03_traceSegment_016_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 2632 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2632 34 34, g32p_row03_traceSegment_016_2632_0034, g32p_row03_traceSegment_016_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 2565 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2565 67 68, g32p_row03_traceSegment_016_2565_0067, g32p_row03_traceSegment_016_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 2430 270 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2430 135 135, g32p_row03_traceSegment_016_2430_0135, g32p_row03_traceSegment_016_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_016 2160 540 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2160 270 270, g32p_row03_traceSegment_016_2160_0270, g32p_row03_traceSegment_016_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 2700 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2716 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2716 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2716 8 9, g32p_row03_traceSegment_016_2716_0008, g32p_row03_traceSegment_016_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 2700 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2700 16 17, g32p_row03_traceSegment_016_2700_0016, g32p_row03_traceSegment_016_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2741 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2733 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2733 8 9, g32p_row03_traceSegment_016_2733_0008, g32p_row03_traceSegment_016_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2750 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2758 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2750 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2750 8 9, g32p_row03_traceSegment_016_2750_0008, g32p_row03_traceSegment_016_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2733 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2733 17 17, g32p_row03_traceSegment_016_2733_0017, g32p_row03_traceSegment_016_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 2700 67 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2700 33 34, g32p_row03_traceSegment_016_2700_0033, g32p_row03_traceSegment_016_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2767 8 9, g32p_row03_traceSegment_016_2767_0008, g32p_row03_traceSegment_016_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2784 8 9, g32p_row03_traceSegment_016_2784_0008, g32p_row03_traceSegment_016_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2767 17 17, g32p_row03_traceSegment_016_2767_0017, g32p_row03_traceSegment_016_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2801 8 9, g32p_row03_traceSegment_016_2801_0008, g32p_row03_traceSegment_016_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2818 8 9, g32p_row03_traceSegment_016_2818_0008, g32p_row03_traceSegment_016_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2801 17 17, g32p_row03_traceSegment_016_2801_0017, g32p_row03_traceSegment_016_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2767 34 34, g32p_row03_traceSegment_016_2767_0034, g32p_row03_traceSegment_016_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 2700 135 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2700 67 68, g32p_row03_traceSegment_016_2700_0067, g32p_row03_traceSegment_016_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 2835 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2859 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2851 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2851 8 9, g32p_row03_traceSegment_016_2851_0008, g32p_row03_traceSegment_016_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 2835 33 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2835 16 17, g32p_row03_traceSegment_016_2835_0016, g32p_row03_traceSegment_016_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2868 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2876 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2868 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2868 8 9, g32p_row03_traceSegment_016_2868_0008, g32p_row03_traceSegment_016_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2885 8 9, g32p_row03_traceSegment_016_2885_0008, g32p_row03_traceSegment_016_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2868 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2868 17 17, g32p_row03_traceSegment_016_2868_0017, g32p_row03_traceSegment_016_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 2835 67 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2835 33 34, g32p_row03_traceSegment_016_2835_0033, g32p_row03_traceSegment_016_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2902 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2910 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2902 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2902 8 9, g32p_row03_traceSegment_016_2902_0008, g32p_row03_traceSegment_016_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2919 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2927 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2919 17 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2919 8 9, g32p_row03_traceSegment_016_2919_0008, g32p_row03_traceSegment_016_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2902 34 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2902 17 17, g32p_row03_traceSegment_016_2902_0017, g32p_row03_traceSegment_016_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2936 8 9, g32p_row03_traceSegment_016_2936_0008, g32p_row03_traceSegment_016_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2961 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2953 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2953 8 9, g32p_row03_traceSegment_016_2953_0008, g32p_row03_traceSegment_016_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 2936 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2936 17 17, g32p_row03_traceSegment_016_2936_0017, g32p_row03_traceSegment_016_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 2902 68 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2902 34 34, g32p_row03_traceSegment_016_2902_0034, g32p_row03_traceSegment_016_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 2835 135 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2835 67 68, g32p_row03_traceSegment_016_2835_0067, g32p_row03_traceSegment_016_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 2700 270 = [0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2700 135 135, g32p_row03_traceSegment_016_2700_0135, g32p_row03_traceSegment_016_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 2970 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 2994 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 2986 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2986 8 9, g32p_row03_traceSegment_016_2986_0008, g32p_row03_traceSegment_016_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 2970 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2970 16 17, g32p_row03_traceSegment_016_2970_0016, g32p_row03_traceSegment_016_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3003 8 9, g32p_row03_traceSegment_016_3003_0008, g32p_row03_traceSegment_016_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3020 8 9, g32p_row03_traceSegment_016_3020_0008, g32p_row03_traceSegment_016_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3003 17 17, g32p_row03_traceSegment_016_3003_0017, g32p_row03_traceSegment_016_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 2970 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2970 33 34, g32p_row03_traceSegment_016_2970_0033, g32p_row03_traceSegment_016_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3037 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3045 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3037 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3037 8 9, g32p_row03_traceSegment_016_3037_0008, g32p_row03_traceSegment_016_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3054 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3062 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3054 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3054 8 9, g32p_row03_traceSegment_016_3054_0008, g32p_row03_traceSegment_016_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3037 34 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3037 17 17, g32p_row03_traceSegment_016_3037_0017, g32p_row03_traceSegment_016_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3071 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3079 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3071 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3071 8 9, g32p_row03_traceSegment_016_3071_0008, g32p_row03_traceSegment_016_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3088 8 9, g32p_row03_traceSegment_016_3088_0008, g32p_row03_traceSegment_016_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3071 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3071 17 17, g32p_row03_traceSegment_016_3071_0017, g32p_row03_traceSegment_016_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 3037 68 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3037 34 34, g32p_row03_traceSegment_016_3037_0034, g32p_row03_traceSegment_016_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 2970 135 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2970 67 68, g32p_row03_traceSegment_016_2970_0067, g32p_row03_traceSegment_016_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 3105 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3121 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3121 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3121 8 9, g32p_row03_traceSegment_016_3121_0008, g32p_row03_traceSegment_016_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 3105 33 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3105 16 17, g32p_row03_traceSegment_016_3105_0016, g32p_row03_traceSegment_016_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3138 8 9, g32p_row03_traceSegment_016_3138_0008, g32p_row03_traceSegment_016_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3155 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3163 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3155 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3155 8 9, g32p_row03_traceSegment_016_3155_0008, g32p_row03_traceSegment_016_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3138 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3138 17 17, g32p_row03_traceSegment_016_3138_0017, g32p_row03_traceSegment_016_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 3105 67 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3105 33 34, g32p_row03_traceSegment_016_3105_0033, g32p_row03_traceSegment_016_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3180 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3172 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3172 8 9, g32p_row03_traceSegment_016_3172_0008, g32p_row03_traceSegment_016_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3197 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3189 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3189 8 9, g32p_row03_traceSegment_016_3189_0008, g32p_row03_traceSegment_016_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3172 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3172 17 17, g32p_row03_traceSegment_016_3172_0017, g32p_row03_traceSegment_016_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3206 8 9, g32p_row03_traceSegment_016_3206_0008, g32p_row03_traceSegment_016_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3223 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3223 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3223 8 9, g32p_row03_traceSegment_016_3223_0008, g32p_row03_traceSegment_016_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3206 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3206 17 17, g32p_row03_traceSegment_016_3206_0017, g32p_row03_traceSegment_016_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 3172 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3172 34 34, g32p_row03_traceSegment_016_3172_0034, g32p_row03_traceSegment_016_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 3105 135 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3105 67 68, g32p_row03_traceSegment_016_3105_0067, g32p_row03_traceSegment_016_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 2970 270 = [0, 0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2970 135 135, g32p_row03_traceSegment_016_2970_0135, g32p_row03_traceSegment_016_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_016 2700 540 = [0, 0, 0, 0, 41] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2700 270 270, g32p_row03_traceSegment_016_2700_0270, g32p_row03_traceSegment_016_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_016 2160 1080 = [0, 0, 0, 0, 51] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2160 540 540, g32p_row03_traceSegment_016_2160_0540, g32p_row03_traceSegment_016_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3264 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3256 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3256 8 9, g32p_row03_traceSegment_016_3256_0008, g32p_row03_traceSegment_016_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 3240 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3240 16 17, g32p_row03_traceSegment_016_3240_0016, g32p_row03_traceSegment_016_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3273 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3273 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3273 8 9, g32p_row03_traceSegment_016_3273_0008, g32p_row03_traceSegment_016_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3290 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3290 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3290 8 9, g32p_row03_traceSegment_016_3290_0008, g32p_row03_traceSegment_016_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3273 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3273 17 17, g32p_row03_traceSegment_016_3273_0017, g32p_row03_traceSegment_016_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 3240 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3240 33 34, g32p_row03_traceSegment_016_3240_0033, g32p_row03_traceSegment_016_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3307 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3307 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3307 8 9, g32p_row03_traceSegment_016_3307_0008, g32p_row03_traceSegment_016_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3324 8 9, g32p_row03_traceSegment_016_3324_0008, g32p_row03_traceSegment_016_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3307 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3307 17 17, g32p_row03_traceSegment_016_3307_0017, g32p_row03_traceSegment_016_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3341 8 9, g32p_row03_traceSegment_016_3341_0008, g32p_row03_traceSegment_016_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3358 8 9, g32p_row03_traceSegment_016_3358_0008, g32p_row03_traceSegment_016_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3341 17 17, g32p_row03_traceSegment_016_3341_0017, g32p_row03_traceSegment_016_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 3307 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3307 34 34, g32p_row03_traceSegment_016_3307_0034, g32p_row03_traceSegment_016_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 3240 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3240 67 68, g32p_row03_traceSegment_016_3240_0067, g32p_row03_traceSegment_016_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 3375 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3391 8 9, g32p_row03_traceSegment_016_3391_0008, g32p_row03_traceSegment_016_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 3375 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3375 16 17, g32p_row03_traceSegment_016_3375_0016, g32p_row03_traceSegment_016_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3408 8 9, g32p_row03_traceSegment_016_3408_0008, g32p_row03_traceSegment_016_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3425 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3425 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3425 8 9, g32p_row03_traceSegment_016_3425_0008, g32p_row03_traceSegment_016_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3408 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3408 17 17, g32p_row03_traceSegment_016_3408_0017, g32p_row03_traceSegment_016_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 3375 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3375 33 34, g32p_row03_traceSegment_016_3375_0033, g32p_row03_traceSegment_016_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3442 8 9, g32p_row03_traceSegment_016_3442_0008, g32p_row03_traceSegment_016_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3459 8 9, g32p_row03_traceSegment_016_3459_0008, g32p_row03_traceSegment_016_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3442 17 17, g32p_row03_traceSegment_016_3442_0017, g32p_row03_traceSegment_016_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3484 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3476 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3476 8 9, g32p_row03_traceSegment_016_3476_0008, g32p_row03_traceSegment_016_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3493 8 9, g32p_row03_traceSegment_016_3493_0008, g32p_row03_traceSegment_016_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3476 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3476 17 17, g32p_row03_traceSegment_016_3476_0017, g32p_row03_traceSegment_016_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 3442 68 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3442 34 34, g32p_row03_traceSegment_016_3442_0034, g32p_row03_traceSegment_016_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 3375 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3375 67 68, g32p_row03_traceSegment_016_3375_0067, g32p_row03_traceSegment_016_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 3240 270 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3240 135 135, g32p_row03_traceSegment_016_3240_0135, g32p_row03_traceSegment_016_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 3510 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3526 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3526 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3526 8 9, g32p_row03_traceSegment_016_3526_0008, g32p_row03_traceSegment_016_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 3510 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3510 16 17, g32p_row03_traceSegment_016_3510_0016, g32p_row03_traceSegment_016_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3543 8 9, g32p_row03_traceSegment_016_3543_0008, g32p_row03_traceSegment_016_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3560 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3560 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3560 8 9, g32p_row03_traceSegment_016_3560_0008, g32p_row03_traceSegment_016_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3543 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3543 17 17, g32p_row03_traceSegment_016_3543_0017, g32p_row03_traceSegment_016_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 3510 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3510 33 34, g32p_row03_traceSegment_016_3510_0033, g32p_row03_traceSegment_016_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3577 8 9, g32p_row03_traceSegment_016_3577_0008, g32p_row03_traceSegment_016_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3594 8 9, g32p_row03_traceSegment_016_3594_0008, g32p_row03_traceSegment_016_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3577 17 17, g32p_row03_traceSegment_016_3577_0017, g32p_row03_traceSegment_016_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3611 8 9, g32p_row03_traceSegment_016_3611_0008, g32p_row03_traceSegment_016_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3636 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3628 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3628 8 9, g32p_row03_traceSegment_016_3628_0008, g32p_row03_traceSegment_016_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3611 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3611 17 17, g32p_row03_traceSegment_016_3611_0017, g32p_row03_traceSegment_016_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 3577 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3577 34 34, g32p_row03_traceSegment_016_3577_0034, g32p_row03_traceSegment_016_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 3510 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3510 67 68, g32p_row03_traceSegment_016_3510_0067, g32p_row03_traceSegment_016_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 3645 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3661 8 9, g32p_row03_traceSegment_016_3661_0008, g32p_row03_traceSegment_016_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 3645 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3645 16 17, g32p_row03_traceSegment_016_3645_0016, g32p_row03_traceSegment_016_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3678 8 9, g32p_row03_traceSegment_016_3678_0008, g32p_row03_traceSegment_016_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3695 8 9, g32p_row03_traceSegment_016_3695_0008, g32p_row03_traceSegment_016_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3678 17 17, g32p_row03_traceSegment_016_3678_0017, g32p_row03_traceSegment_016_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 3645 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3645 33 34, g32p_row03_traceSegment_016_3645_0033, g32p_row03_traceSegment_016_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3712 8 9, g32p_row03_traceSegment_016_3712_0008, g32p_row03_traceSegment_016_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3729 8 9, g32p_row03_traceSegment_016_3729_0008, g32p_row03_traceSegment_016_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3712 17 17, g32p_row03_traceSegment_016_3712_0017, g32p_row03_traceSegment_016_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3746 8 9, g32p_row03_traceSegment_016_3746_0008, g32p_row03_traceSegment_016_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3763 8 9, g32p_row03_traceSegment_016_3763_0008, g32p_row03_traceSegment_016_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3746 17 17, g32p_row03_traceSegment_016_3746_0017, g32p_row03_traceSegment_016_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3712 34 34, g32p_row03_traceSegment_016_3712_0034, g32p_row03_traceSegment_016_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 3645 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3645 67 68, g32p_row03_traceSegment_016_3645_0067, g32p_row03_traceSegment_016_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 3510 270 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3510 135 135, g32p_row03_traceSegment_016_3510_0135, g32p_row03_traceSegment_016_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_016 3240 540 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3240 270 270, g32p_row03_traceSegment_016_3240_0270, g32p_row03_traceSegment_016_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3796 8 9, g32p_row03_traceSegment_016_3796_0008, g32p_row03_traceSegment_016_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3780 16 17, g32p_row03_traceSegment_016_3780_0016, g32p_row03_traceSegment_016_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3813 8 9, g32p_row03_traceSegment_016_3813_0008, g32p_row03_traceSegment_016_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3830 8 9, g32p_row03_traceSegment_016_3830_0008, g32p_row03_traceSegment_016_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3813 17 17, g32p_row03_traceSegment_016_3813_0017, g32p_row03_traceSegment_016_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3780 33 34, g32p_row03_traceSegment_016_3780_0033, g32p_row03_traceSegment_016_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3847 8 9, g32p_row03_traceSegment_016_3847_0008, g32p_row03_traceSegment_016_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3872 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3864 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3864 8 9, g32p_row03_traceSegment_016_3864_0008, g32p_row03_traceSegment_016_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3847 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3847 17 17, g32p_row03_traceSegment_016_3847_0017, g32p_row03_traceSegment_016_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3881 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3881 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3881 8 9, g32p_row03_traceSegment_016_3881_0008, g32p_row03_traceSegment_016_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3898 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3898 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3898 8 9, g32p_row03_traceSegment_016_3898_0008, g32p_row03_traceSegment_016_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3881 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3881 17 17, g32p_row03_traceSegment_016_3881_0017, g32p_row03_traceSegment_016_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 3847 68 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3847 34 34, g32p_row03_traceSegment_016_3847_0034, g32p_row03_traceSegment_016_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 3780 135 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3780 67 68, g32p_row03_traceSegment_016_3780_0067, g32p_row03_traceSegment_016_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3931 8 9, g32p_row03_traceSegment_016_3931_0008, g32p_row03_traceSegment_016_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3915 16 17, g32p_row03_traceSegment_016_3915_0016, g32p_row03_traceSegment_016_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3956 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3948 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3948 8 9, g32p_row03_traceSegment_016_3948_0008, g32p_row03_traceSegment_016_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3965 8 9, g32p_row03_traceSegment_016_3965_0008, g32p_row03_traceSegment_016_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3948 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3948 17 17, g32p_row03_traceSegment_016_3948_0017, g32p_row03_traceSegment_016_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 3915 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3915 33 34, g32p_row03_traceSegment_016_3915_0033, g32p_row03_traceSegment_016_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3982 8 9, g32p_row03_traceSegment_016_3982_0008, g32p_row03_traceSegment_016_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3999 8 9, g32p_row03_traceSegment_016_3999_0008, g32p_row03_traceSegment_016_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3982 17 17, g32p_row03_traceSegment_016_3982_0017, g32p_row03_traceSegment_016_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4016 8 9, g32p_row03_traceSegment_016_4016_0008, g32p_row03_traceSegment_016_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4033 8 9, g32p_row03_traceSegment_016_4033_0008, g32p_row03_traceSegment_016_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4016 17 17, g32p_row03_traceSegment_016_4016_0017, g32p_row03_traceSegment_016_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3982 34 34, g32p_row03_traceSegment_016_3982_0034, g32p_row03_traceSegment_016_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 3915 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3915 67 68, g32p_row03_traceSegment_016_3915_0067, g32p_row03_traceSegment_016_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 3780 270 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3780 135 135, g32p_row03_traceSegment_016_3780_0135, g32p_row03_traceSegment_016_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 4050 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4066 8 9, g32p_row03_traceSegment_016_4066_0008, g32p_row03_traceSegment_016_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 4050 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4050 16 17, g32p_row03_traceSegment_016_4050_0016, g32p_row03_traceSegment_016_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4083 8 9, g32p_row03_traceSegment_016_4083_0008, g32p_row03_traceSegment_016_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4108 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4100 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4100 8 9, g32p_row03_traceSegment_016_4100_0008, g32p_row03_traceSegment_016_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 4083 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4083 17 17, g32p_row03_traceSegment_016_4083_0017, g32p_row03_traceSegment_016_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 4050 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4050 33 34, g32p_row03_traceSegment_016_4050_0033, g32p_row03_traceSegment_016_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4125 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4117 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4117 8 9, g32p_row03_traceSegment_016_4117_0008, g32p_row03_traceSegment_016_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4134 8 9, g32p_row03_traceSegment_016_4134_0008, g32p_row03_traceSegment_016_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 4117 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4117 17 17, g32p_row03_traceSegment_016_4117_0017, g32p_row03_traceSegment_016_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4151 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4151 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4151 8 9, g32p_row03_traceSegment_016_4151_0008, g32p_row03_traceSegment_016_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4168 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4168 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4168 8 9, g32p_row03_traceSegment_016_4168_0008, g32p_row03_traceSegment_016_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 4151 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4151 17 17, g32p_row03_traceSegment_016_4151_0017, g32p_row03_traceSegment_016_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 4117 68 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4117 34 34, g32p_row03_traceSegment_016_4117_0034, g32p_row03_traceSegment_016_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 4050 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4050 67 68, g32p_row03_traceSegment_016_4050_0067, g32p_row03_traceSegment_016_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_016 4185 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4201 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4201 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4201 8 9, g32p_row03_traceSegment_016_4201_0008, g32p_row03_traceSegment_016_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_016 4185 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4185 16 17, g32p_row03_traceSegment_016_4185_0016, g32p_row03_traceSegment_016_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4218 8 9, g32p_row03_traceSegment_016_4218_0008, g32p_row03_traceSegment_016_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4235 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4235 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4235 8 9, g32p_row03_traceSegment_016_4235_0008, g32p_row03_traceSegment_016_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 4218 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4218 17 17, g32p_row03_traceSegment_016_4218_0017, g32p_row03_traceSegment_016_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_016 4185 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4185 33 34, g32p_row03_traceSegment_016_4185_0033, g32p_row03_traceSegment_016_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4252 8 9, g32p_row03_traceSegment_016_4252_0008, g32p_row03_traceSegment_016_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4269 8 9, g32p_row03_traceSegment_016_4269_0008, g32p_row03_traceSegment_016_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4252 17 17, g32p_row03_traceSegment_016_4252_0017, g32p_row03_traceSegment_016_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4286 8 9, g32p_row03_traceSegment_016_4286_0008, g32p_row03_traceSegment_016_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_016 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_016 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_016_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_016 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4303 8 9, g32p_row03_traceSegment_016_4303_0008, g32p_row03_traceSegment_016_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_016 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4286 17 17, g32p_row03_traceSegment_016_4286_0017, g32p_row03_traceSegment_016_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_016 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4252 34 34, g32p_row03_traceSegment_016_4252_0034, g32p_row03_traceSegment_016_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_016 4185 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4185 67 68, g32p_row03_traceSegment_016_4185_0067, g32p_row03_traceSegment_016_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_016_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_016 4050 270 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 4050 135 135, g32p_row03_traceSegment_016_4050_0135, g32p_row03_traceSegment_016_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_016 3780 540 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3780 270 270, g32p_row03_traceSegment_016_3780_0270, g32p_row03_traceSegment_016_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_016_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_016 3240 1080 = [0, 0, 0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 3240 540 540, g32p_row03_traceSegment_016_3240_0540, g32p_row03_traceSegment_016_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_016_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_016 2160 2160 = [0, 0, 0, 0, 78] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 2160 1080 1080, g32p_row03_traceSegment_016_2160_1080, g32p_row03_traceSegment_016_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_016_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_016 0 4320 = [0, 0, 0, 0, 144] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_016 0 2160 2160, g32p_row03_traceSegment_016_0000_2160, g32p_row03_traceSegment_016_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_016 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 16 = [0, 0, 0, 0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_016_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 0) (g32p_literalTraceValue 2 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_000]
  decide +kernel

theorem g32p_row03_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 4) (g32p_literalTraceValue 2 4)
      [1, -1, 1] [25920, 25920, 25920] = true := by
  rw [g32p_row03_traceCoefficients_004]
  decide +kernel

theorem g32p_row03_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 6) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 6) (g32p_literalTraceValue 2 6)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_006]
  decide +kernel

theorem g32p_row03_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 10) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 10) (g32p_literalTraceValue 2 10)
      [1, -1, 1] [0, 0, 12960, 12960] = true := by
  rw [g32p_row03_traceCoefficients_010]
  decide +kernel

theorem g32p_row03_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 11) (g32p_literalTraceValue 2 11)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_011]
  decide +kernel

theorem g32p_row03_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 13) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 13) (g32p_literalTraceValue 2 13)
      [1, -1, 1] [0, 0, 8640, 8640] = true := by
  rw [g32p_row03_traceCoefficients_013]
  decide +kernel

theorem g32p_row03_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 15) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 15) (g32p_literalTraceValue 2 15)
      [1, -1, 1] [-12960] = true := by
  rw [g32p_row03_traceCoefficients_015]
  decide +kernel

theorem g32p_row03_tracePolynomial_016 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 16) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 16) (g32p_literalTraceValue 2 16)
      [1, -1, 1] [4320, 4320, 4320] = true := by
  rw [g32p_row03_traceCoefficients_016]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
