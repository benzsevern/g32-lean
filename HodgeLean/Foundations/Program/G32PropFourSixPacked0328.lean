import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_066 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 66 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_066_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 16 8 9, g32p_row03_traceSegment_066_0016_0008, g32p_row03_traceSegment_066_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 0 16 17, g32p_row03_traceSegment_066_0000_0016, g32p_row03_traceSegment_066_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 33 8 9, g32p_row03_traceSegment_066_0033_0008, g32p_row03_traceSegment_066_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 50 8 9, g32p_row03_traceSegment_066_0050_0008, g32p_row03_traceSegment_066_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 33 17 17, g32p_row03_traceSegment_066_0033_0017, g32p_row03_traceSegment_066_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 0 33 34, g32p_row03_traceSegment_066_0000_0033, g32p_row03_traceSegment_066_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 67 8 9, g32p_row03_traceSegment_066_0067_0008, g32p_row03_traceSegment_066_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 84 8 9, g32p_row03_traceSegment_066_0084_0008, g32p_row03_traceSegment_066_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 67 17 17, g32p_row03_traceSegment_066_0067_0017, g32p_row03_traceSegment_066_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 101 8 9, g32p_row03_traceSegment_066_0101_0008, g32p_row03_traceSegment_066_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 118 8 9, g32p_row03_traceSegment_066_0118_0008, g32p_row03_traceSegment_066_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 101 17 17, g32p_row03_traceSegment_066_0101_0017, g32p_row03_traceSegment_066_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 67 34 34, g32p_row03_traceSegment_066_0067_0034, g32p_row03_traceSegment_066_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 0 67 68, g32p_row03_traceSegment_066_0000_0067, g32p_row03_traceSegment_066_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 151 8 9, g32p_row03_traceSegment_066_0151_0008, g32p_row03_traceSegment_066_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 135 16 17, g32p_row03_traceSegment_066_0135_0016, g32p_row03_traceSegment_066_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 168 8 9, g32p_row03_traceSegment_066_0168_0008, g32p_row03_traceSegment_066_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 185 8 9, g32p_row03_traceSegment_066_0185_0008, g32p_row03_traceSegment_066_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 168 17 17, g32p_row03_traceSegment_066_0168_0017, g32p_row03_traceSegment_066_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 135 33 34, g32p_row03_traceSegment_066_0135_0033, g32p_row03_traceSegment_066_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 202 8 9, g32p_row03_traceSegment_066_0202_0008, g32p_row03_traceSegment_066_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 219 8 9, g32p_row03_traceSegment_066_0219_0008, g32p_row03_traceSegment_066_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 202 17 17, g32p_row03_traceSegment_066_0202_0017, g32p_row03_traceSegment_066_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 236 8 9, g32p_row03_traceSegment_066_0236_0008, g32p_row03_traceSegment_066_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 253 8 9, g32p_row03_traceSegment_066_0253_0008, g32p_row03_traceSegment_066_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 236 17 17, g32p_row03_traceSegment_066_0236_0017, g32p_row03_traceSegment_066_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 202 34 34, g32p_row03_traceSegment_066_0202_0034, g32p_row03_traceSegment_066_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 135 67 68, g32p_row03_traceSegment_066_0135_0067, g32p_row03_traceSegment_066_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 0 135 135, g32p_row03_traceSegment_066_0000_0135, g32p_row03_traceSegment_066_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 286 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 294 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 286 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 286 8 9, g32p_row03_traceSegment_066_0286_0008, g32p_row03_traceSegment_066_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 270 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 270 16 17, g32p_row03_traceSegment_066_0270_0016, g32p_row03_traceSegment_066_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 311 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 303 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 303 8 9, g32p_row03_traceSegment_066_0303_0008, g32p_row03_traceSegment_066_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 320 8 9, g32p_row03_traceSegment_066_0320_0008, g32p_row03_traceSegment_066_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 303 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 303 17 17, g32p_row03_traceSegment_066_0303_0017, g32p_row03_traceSegment_066_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 270 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 270 33 34, g32p_row03_traceSegment_066_0270_0033, g32p_row03_traceSegment_066_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 345 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 337 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 337 8 9, g32p_row03_traceSegment_066_0337_0008, g32p_row03_traceSegment_066_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 354 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 354 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 354 8 9, g32p_row03_traceSegment_066_0354_0008, g32p_row03_traceSegment_066_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 337 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 337 17 17, g32p_row03_traceSegment_066_0337_0017, g32p_row03_traceSegment_066_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 371 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 371 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 371 8 9, g32p_row03_traceSegment_066_0371_0008, g32p_row03_traceSegment_066_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 388 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 388 8 9, g32p_row03_traceSegment_066_0388_0008, g32p_row03_traceSegment_066_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 371 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 371 17 17, g32p_row03_traceSegment_066_0371_0017, g32p_row03_traceSegment_066_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 337 68 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 337 34 34, g32p_row03_traceSegment_066_0337_0034, g32p_row03_traceSegment_066_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 270 135 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 270 67 68, g32p_row03_traceSegment_066_0270_0067, g32p_row03_traceSegment_066_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 421 8 9, g32p_row03_traceSegment_066_0421_0008, g32p_row03_traceSegment_066_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 405 16 17, g32p_row03_traceSegment_066_0405_0016, g32p_row03_traceSegment_066_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 438 8 9, g32p_row03_traceSegment_066_0438_0008, g32p_row03_traceSegment_066_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 455 8 9, g32p_row03_traceSegment_066_0455_0008, g32p_row03_traceSegment_066_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 438 17 17, g32p_row03_traceSegment_066_0438_0017, g32p_row03_traceSegment_066_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 405 33 34, g32p_row03_traceSegment_066_0405_0033, g32p_row03_traceSegment_066_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 472 8 9, g32p_row03_traceSegment_066_0472_0008, g32p_row03_traceSegment_066_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 489 8 9, g32p_row03_traceSegment_066_0489_0008, g32p_row03_traceSegment_066_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 472 17 17, g32p_row03_traceSegment_066_0472_0017, g32p_row03_traceSegment_066_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 506 8 9, g32p_row03_traceSegment_066_0506_0008, g32p_row03_traceSegment_066_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 523 8 9, g32p_row03_traceSegment_066_0523_0008, g32p_row03_traceSegment_066_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 506 17 17, g32p_row03_traceSegment_066_0506_0017, g32p_row03_traceSegment_066_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 472 34 34, g32p_row03_traceSegment_066_0472_0034, g32p_row03_traceSegment_066_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 405 67 68, g32p_row03_traceSegment_066_0405_0067, g32p_row03_traceSegment_066_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 270 270 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 270 135 135, g32p_row03_traceSegment_066_0270_0135, g32p_row03_traceSegment_066_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_066 0 540 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 0 270 270, g32p_row03_traceSegment_066_0000_0270, g32p_row03_traceSegment_066_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 556 8 9, g32p_row03_traceSegment_066_0556_0008, g32p_row03_traceSegment_066_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 540 16 17, g32p_row03_traceSegment_066_0540_0016, g32p_row03_traceSegment_066_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 573 8 9, g32p_row03_traceSegment_066_0573_0008, g32p_row03_traceSegment_066_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 590 8 9, g32p_row03_traceSegment_066_0590_0008, g32p_row03_traceSegment_066_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 573 17 17, g32p_row03_traceSegment_066_0573_0017, g32p_row03_traceSegment_066_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 540 33 34, g32p_row03_traceSegment_066_0540_0033, g32p_row03_traceSegment_066_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 607 8 9, g32p_row03_traceSegment_066_0607_0008, g32p_row03_traceSegment_066_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 624 8 9, g32p_row03_traceSegment_066_0624_0008, g32p_row03_traceSegment_066_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 607 17 17, g32p_row03_traceSegment_066_0607_0017, g32p_row03_traceSegment_066_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 641 8 9, g32p_row03_traceSegment_066_0641_0008, g32p_row03_traceSegment_066_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 658 8 9, g32p_row03_traceSegment_066_0658_0008, g32p_row03_traceSegment_066_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 641 17 17, g32p_row03_traceSegment_066_0641_0017, g32p_row03_traceSegment_066_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 607 34 34, g32p_row03_traceSegment_066_0607_0034, g32p_row03_traceSegment_066_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 540 67 68, g32p_row03_traceSegment_066_0540_0067, g32p_row03_traceSegment_066_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 691 8 9, g32p_row03_traceSegment_066_0691_0008, g32p_row03_traceSegment_066_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 675 16 17, g32p_row03_traceSegment_066_0675_0016, g32p_row03_traceSegment_066_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 708 8 9, g32p_row03_traceSegment_066_0708_0008, g32p_row03_traceSegment_066_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 725 8 9, g32p_row03_traceSegment_066_0725_0008, g32p_row03_traceSegment_066_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 708 17 17, g32p_row03_traceSegment_066_0708_0017, g32p_row03_traceSegment_066_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 675 33 34, g32p_row03_traceSegment_066_0675_0033, g32p_row03_traceSegment_066_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 742 8 9, g32p_row03_traceSegment_066_0742_0008, g32p_row03_traceSegment_066_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 759 8 9, g32p_row03_traceSegment_066_0759_0008, g32p_row03_traceSegment_066_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 742 17 17, g32p_row03_traceSegment_066_0742_0017, g32p_row03_traceSegment_066_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 784 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 776 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 776 8 9, g32p_row03_traceSegment_066_0776_0008, g32p_row03_traceSegment_066_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 793 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 793 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 793 8 9, g32p_row03_traceSegment_066_0793_0008, g32p_row03_traceSegment_066_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 776 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 776 17 17, g32p_row03_traceSegment_066_0776_0017, g32p_row03_traceSegment_066_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 742 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 742 34 34, g32p_row03_traceSegment_066_0742_0034, g32p_row03_traceSegment_066_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 675 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 675 67 68, g32p_row03_traceSegment_066_0675_0067, g32p_row03_traceSegment_066_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 540 270 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 540 135 135, g32p_row03_traceSegment_066_0540_0135, g32p_row03_traceSegment_066_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 834 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 826 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 826 8 9, g32p_row03_traceSegment_066_0826_0008, g32p_row03_traceSegment_066_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 810 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 810 16 17, g32p_row03_traceSegment_066_0810_0016, g32p_row03_traceSegment_066_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 843 8 9, g32p_row03_traceSegment_066_0843_0008, g32p_row03_traceSegment_066_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 860 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 860 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 860 8 9, g32p_row03_traceSegment_066_0860_0008, g32p_row03_traceSegment_066_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 843 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 843 17 17, g32p_row03_traceSegment_066_0843_0017, g32p_row03_traceSegment_066_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 810 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 810 33 34, g32p_row03_traceSegment_066_0810_0033, g32p_row03_traceSegment_066_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 885 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 877 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 877 8 9, g32p_row03_traceSegment_066_0877_0008, g32p_row03_traceSegment_066_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 894 8 9, g32p_row03_traceSegment_066_0894_0008, g32p_row03_traceSegment_066_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 877 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 877 17 17, g32p_row03_traceSegment_066_0877_0017, g32p_row03_traceSegment_066_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 911 8 9, g32p_row03_traceSegment_066_0911_0008, g32p_row03_traceSegment_066_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 936 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 928 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 928 8 9, g32p_row03_traceSegment_066_0928_0008, g32p_row03_traceSegment_066_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 911 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 911 17 17, g32p_row03_traceSegment_066_0911_0017, g32p_row03_traceSegment_066_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 877 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 877 34 34, g32p_row03_traceSegment_066_0877_0034, g32p_row03_traceSegment_066_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 810 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 810 67 68, g32p_row03_traceSegment_066_0810_0067, g32p_row03_traceSegment_066_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 945 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 969 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 961 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 961 8 9, g32p_row03_traceSegment_066_0961_0008, g32p_row03_traceSegment_066_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 945 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 945 16 17, g32p_row03_traceSegment_066_0945_0016, g32p_row03_traceSegment_066_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 978 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 986 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 978 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 978 8 9, g32p_row03_traceSegment_066_0978_0008, g32p_row03_traceSegment_066_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 995 8 9, g32p_row03_traceSegment_066_0995_0008, g32p_row03_traceSegment_066_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 978 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 978 17 17, g32p_row03_traceSegment_066_0978_0017, g32p_row03_traceSegment_066_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 945 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 945 33 34, g32p_row03_traceSegment_066_0945_0033, g32p_row03_traceSegment_066_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1012 8 9, g32p_row03_traceSegment_066_1012_0008, g32p_row03_traceSegment_066_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1029 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1029 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1029 8 9, g32p_row03_traceSegment_066_1029_0008, g32p_row03_traceSegment_066_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1012 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1012 17 17, g32p_row03_traceSegment_066_1012_0017, g32p_row03_traceSegment_066_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1046 8 9, g32p_row03_traceSegment_066_1046_0008, g32p_row03_traceSegment_066_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1071 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1063 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1063 8 9, g32p_row03_traceSegment_066_1063_0008, g32p_row03_traceSegment_066_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1046 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1046 17 17, g32p_row03_traceSegment_066_1046_0017, g32p_row03_traceSegment_066_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 1012 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1012 34 34, g32p_row03_traceSegment_066_1012_0034, g32p_row03_traceSegment_066_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 945 135 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 945 67 68, g32p_row03_traceSegment_066_0945_0067, g32p_row03_traceSegment_066_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 810 270 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 810 135 135, g32p_row03_traceSegment_066_0810_0135, g32p_row03_traceSegment_066_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_066 540 540 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 540 270 270, g32p_row03_traceSegment_066_0540_0270, g32p_row03_traceSegment_066_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_066 0 1080 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 0 540 540, g32p_row03_traceSegment_066_0000_0540, g32p_row03_traceSegment_066_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1104 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1096 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1096 8 9, g32p_row03_traceSegment_066_1096_0008, g32p_row03_traceSegment_066_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 1080 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1080 16 17, g32p_row03_traceSegment_066_1080_0016, g32p_row03_traceSegment_066_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1113 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1121 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1113 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1113 8 9, g32p_row03_traceSegment_066_1113_0008, g32p_row03_traceSegment_066_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1130 8 9, g32p_row03_traceSegment_066_1130_0008, g32p_row03_traceSegment_066_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1113 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1113 17 17, g32p_row03_traceSegment_066_1113_0017, g32p_row03_traceSegment_066_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 1080 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1080 33 34, g32p_row03_traceSegment_066_1080_0033, g32p_row03_traceSegment_066_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1147 8 9, g32p_row03_traceSegment_066_1147_0008, g32p_row03_traceSegment_066_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1172 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1164 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1164 8 9, g32p_row03_traceSegment_066_1164_0008, g32p_row03_traceSegment_066_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1147 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1147 17 17, g32p_row03_traceSegment_066_1147_0017, g32p_row03_traceSegment_066_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1189 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1181 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1181 8 9, g32p_row03_traceSegment_066_1181_0008, g32p_row03_traceSegment_066_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1198 8 9, g32p_row03_traceSegment_066_1198_0008, g32p_row03_traceSegment_066_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1181 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1181 17 17, g32p_row03_traceSegment_066_1181_0017, g32p_row03_traceSegment_066_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 1147 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1147 34 34, g32p_row03_traceSegment_066_1147_0034, g32p_row03_traceSegment_066_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 1080 135 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1080 67 68, g32p_row03_traceSegment_066_1080_0067, g32p_row03_traceSegment_066_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1231 8 9, g32p_row03_traceSegment_066_1231_0008, g32p_row03_traceSegment_066_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1215 16 17, g32p_row03_traceSegment_066_1215_0016, g32p_row03_traceSegment_066_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1248 8 9, g32p_row03_traceSegment_066_1248_0008, g32p_row03_traceSegment_066_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1265 8 9, g32p_row03_traceSegment_066_1265_0008, g32p_row03_traceSegment_066_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1248 17 17, g32p_row03_traceSegment_066_1248_0017, g32p_row03_traceSegment_066_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1215 33 34, g32p_row03_traceSegment_066_1215_0033, g32p_row03_traceSegment_066_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1282 8 9, g32p_row03_traceSegment_066_1282_0008, g32p_row03_traceSegment_066_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1299 8 9, g32p_row03_traceSegment_066_1299_0008, g32p_row03_traceSegment_066_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1282 17 17, g32p_row03_traceSegment_066_1282_0017, g32p_row03_traceSegment_066_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1316 8 9, g32p_row03_traceSegment_066_1316_0008, g32p_row03_traceSegment_066_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1333 8 9, g32p_row03_traceSegment_066_1333_0008, g32p_row03_traceSegment_066_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1316 17 17, g32p_row03_traceSegment_066_1316_0017, g32p_row03_traceSegment_066_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1282 34 34, g32p_row03_traceSegment_066_1282_0034, g32p_row03_traceSegment_066_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1215 67 68, g32p_row03_traceSegment_066_1215_0067, g32p_row03_traceSegment_066_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 1080 270 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1080 135 135, g32p_row03_traceSegment_066_1080_0135, g32p_row03_traceSegment_066_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1366 8 9, g32p_row03_traceSegment_066_1366_0008, g32p_row03_traceSegment_066_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1350 16 17, g32p_row03_traceSegment_066_1350_0016, g32p_row03_traceSegment_066_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1383 8 9, g32p_row03_traceSegment_066_1383_0008, g32p_row03_traceSegment_066_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1400 8 9, g32p_row03_traceSegment_066_1400_0008, g32p_row03_traceSegment_066_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1383 17 17, g32p_row03_traceSegment_066_1383_0017, g32p_row03_traceSegment_066_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1350 33 34, g32p_row03_traceSegment_066_1350_0033, g32p_row03_traceSegment_066_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1417 8 9, g32p_row03_traceSegment_066_1417_0008, g32p_row03_traceSegment_066_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1434 8 9, g32p_row03_traceSegment_066_1434_0008, g32p_row03_traceSegment_066_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1417 17 17, g32p_row03_traceSegment_066_1417_0017, g32p_row03_traceSegment_066_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1451 8 9, g32p_row03_traceSegment_066_1451_0008, g32p_row03_traceSegment_066_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1468 8 9, g32p_row03_traceSegment_066_1468_0008, g32p_row03_traceSegment_066_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1451 17 17, g32p_row03_traceSegment_066_1451_0017, g32p_row03_traceSegment_066_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1417 34 34, g32p_row03_traceSegment_066_1417_0034, g32p_row03_traceSegment_066_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1350 67 68, g32p_row03_traceSegment_066_1350_0067, g32p_row03_traceSegment_066_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 1485 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1501 8 9, g32p_row03_traceSegment_066_1501_0008, g32p_row03_traceSegment_066_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 1485 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1485 16 17, g32p_row03_traceSegment_066_1485_0016, g32p_row03_traceSegment_066_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1518 8 9, g32p_row03_traceSegment_066_1518_0008, g32p_row03_traceSegment_066_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1543 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1535 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1535 8 9, g32p_row03_traceSegment_066_1535_0008, g32p_row03_traceSegment_066_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1518 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1518 17 17, g32p_row03_traceSegment_066_1518_0017, g32p_row03_traceSegment_066_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 1485 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1485 33 34, g32p_row03_traceSegment_066_1485_0033, g32p_row03_traceSegment_066_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1552 8 9, g32p_row03_traceSegment_066_1552_0008, g32p_row03_traceSegment_066_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1569 8 9, g32p_row03_traceSegment_066_1569_0008, g32p_row03_traceSegment_066_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1552 17 17, g32p_row03_traceSegment_066_1552_0017, g32p_row03_traceSegment_066_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1586 8 9, g32p_row03_traceSegment_066_1586_0008, g32p_row03_traceSegment_066_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1603 8 9, g32p_row03_traceSegment_066_1603_0008, g32p_row03_traceSegment_066_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1586 17 17, g32p_row03_traceSegment_066_1586_0017, g32p_row03_traceSegment_066_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1552 34 34, g32p_row03_traceSegment_066_1552_0034, g32p_row03_traceSegment_066_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 1485 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1485 67 68, g32p_row03_traceSegment_066_1485_0067, g32p_row03_traceSegment_066_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 1350 270 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1350 135 135, g32p_row03_traceSegment_066_1350_0135, g32p_row03_traceSegment_066_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_066 1080 540 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1080 270 270, g32p_row03_traceSegment_066_1080_0270, g32p_row03_traceSegment_066_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1636 8 9, g32p_row03_traceSegment_066_1636_0008, g32p_row03_traceSegment_066_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1620 16 17, g32p_row03_traceSegment_066_1620_0016, g32p_row03_traceSegment_066_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1653 8 9, g32p_row03_traceSegment_066_1653_0008, g32p_row03_traceSegment_066_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1670 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1670 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1670 8 9, g32p_row03_traceSegment_066_1670_0008, g32p_row03_traceSegment_066_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1653 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1653 17 17, g32p_row03_traceSegment_066_1653_0017, g32p_row03_traceSegment_066_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 1620 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1620 33 34, g32p_row03_traceSegment_066_1620_0033, g32p_row03_traceSegment_066_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1687 8 9, g32p_row03_traceSegment_066_1687_0008, g32p_row03_traceSegment_066_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1704 8 9, g32p_row03_traceSegment_066_1704_0008, g32p_row03_traceSegment_066_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1687 17 17, g32p_row03_traceSegment_066_1687_0017, g32p_row03_traceSegment_066_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1721 8 9, g32p_row03_traceSegment_066_1721_0008, g32p_row03_traceSegment_066_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1738 8 9, g32p_row03_traceSegment_066_1738_0008, g32p_row03_traceSegment_066_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1721 17 17, g32p_row03_traceSegment_066_1721_0017, g32p_row03_traceSegment_066_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1687 34 34, g32p_row03_traceSegment_066_1687_0034, g32p_row03_traceSegment_066_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 1620 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1620 67 68, g32p_row03_traceSegment_066_1620_0067, g32p_row03_traceSegment_066_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 1755 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1771 8 9, g32p_row03_traceSegment_066_1771_0008, g32p_row03_traceSegment_066_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 1755 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1755 16 17, g32p_row03_traceSegment_066_1755_0016, g32p_row03_traceSegment_066_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1788 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1788 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1788 8 9, g32p_row03_traceSegment_066_1788_0008, g32p_row03_traceSegment_066_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1805 8 9, g32p_row03_traceSegment_066_1805_0008, g32p_row03_traceSegment_066_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1788 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1788 17 17, g32p_row03_traceSegment_066_1788_0017, g32p_row03_traceSegment_066_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 1755 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1755 33 34, g32p_row03_traceSegment_066_1755_0033, g32p_row03_traceSegment_066_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1822 8 9, g32p_row03_traceSegment_066_1822_0008, g32p_row03_traceSegment_066_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1839 8 9, g32p_row03_traceSegment_066_1839_0008, g32p_row03_traceSegment_066_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1822 17 17, g32p_row03_traceSegment_066_1822_0017, g32p_row03_traceSegment_066_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1856 8 9, g32p_row03_traceSegment_066_1856_0008, g32p_row03_traceSegment_066_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1873 8 9, g32p_row03_traceSegment_066_1873_0008, g32p_row03_traceSegment_066_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1856 17 17, g32p_row03_traceSegment_066_1856_0017, g32p_row03_traceSegment_066_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1822 34 34, g32p_row03_traceSegment_066_1822_0034, g32p_row03_traceSegment_066_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 1755 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1755 67 68, g32p_row03_traceSegment_066_1755_0067, g32p_row03_traceSegment_066_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 1620 270 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1620 135 135, g32p_row03_traceSegment_066_1620_0135, g32p_row03_traceSegment_066_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 1890 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1914 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1906 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1906 8 9, g32p_row03_traceSegment_066_1906_0008, g32p_row03_traceSegment_066_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 1890 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1890 16 17, g32p_row03_traceSegment_066_1890_0016, g32p_row03_traceSegment_066_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1923 8 9, g32p_row03_traceSegment_066_1923_0008, g32p_row03_traceSegment_066_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1940 8 9, g32p_row03_traceSegment_066_1940_0008, g32p_row03_traceSegment_066_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1923 17 17, g32p_row03_traceSegment_066_1923_0017, g32p_row03_traceSegment_066_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 1890 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1890 33 34, g32p_row03_traceSegment_066_1890_0033, g32p_row03_traceSegment_066_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1957 8 9, g32p_row03_traceSegment_066_1957_0008, g32p_row03_traceSegment_066_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1974 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1982 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1974 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1974 8 9, g32p_row03_traceSegment_066_1974_0008, g32p_row03_traceSegment_066_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1957 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1957 17 17, g32p_row03_traceSegment_066_1957_0017, g32p_row03_traceSegment_066_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1991 8 9, g32p_row03_traceSegment_066_1991_0008, g32p_row03_traceSegment_066_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2016 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2008 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2008 8 9, g32p_row03_traceSegment_066_2008_0008, g32p_row03_traceSegment_066_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 1991 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1991 17 17, g32p_row03_traceSegment_066_1991_0017, g32p_row03_traceSegment_066_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 1957 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1957 34 34, g32p_row03_traceSegment_066_1957_0034, g32p_row03_traceSegment_066_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 1890 135 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1890 67 68, g32p_row03_traceSegment_066_1890_0067, g32p_row03_traceSegment_066_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 2025 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2041 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2049 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2041 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2041 8 9, g32p_row03_traceSegment_066_2041_0008, g32p_row03_traceSegment_066_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 2025 33 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2025 16 17, g32p_row03_traceSegment_066_2025_0016, g32p_row03_traceSegment_066_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2058 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2066 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2058 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2058 8 9, g32p_row03_traceSegment_066_2058_0008, g32p_row03_traceSegment_066_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2075 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2083 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2075 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2075 8 9, g32p_row03_traceSegment_066_2075_0008, g32p_row03_traceSegment_066_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2058 34 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2058 17 17, g32p_row03_traceSegment_066_2058_0017, g32p_row03_traceSegment_066_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 2025 67 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2025 33 34, g32p_row03_traceSegment_066_2025_0033, g32p_row03_traceSegment_066_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2092 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2100 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2092 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2092 8 9, g32p_row03_traceSegment_066_2092_0008, g32p_row03_traceSegment_066_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2117 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2109 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2109 8 9, g32p_row03_traceSegment_066_2109_0008, g32p_row03_traceSegment_066_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2092 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2092 17 17, g32p_row03_traceSegment_066_2092_0017, g32p_row03_traceSegment_066_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2126 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2126 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2126 8 9, g32p_row03_traceSegment_066_2126_0008, g32p_row03_traceSegment_066_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2151 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2143 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2143 8 9, g32p_row03_traceSegment_066_2143_0008, g32p_row03_traceSegment_066_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2126 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2126 17 17, g32p_row03_traceSegment_066_2126_0017, g32p_row03_traceSegment_066_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 2092 68 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2092 34 34, g32p_row03_traceSegment_066_2092_0034, g32p_row03_traceSegment_066_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 2025 135 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2025 67 68, g32p_row03_traceSegment_066_2025_0067, g32p_row03_traceSegment_066_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 1890 270 = [0, 25] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1890 135 135, g32p_row03_traceSegment_066_1890_0135, g32p_row03_traceSegment_066_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_066 1620 540 = [0, 28] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1620 270 270, g32p_row03_traceSegment_066_1620_0270, g32p_row03_traceSegment_066_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_066_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_066 1080 1080 = [0, 36] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 1080 540 540, g32p_row03_traceSegment_066_1080_0540, g32p_row03_traceSegment_066_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_066 0 2160 = [0, 56] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 0 1080 1080, g32p_row03_traceSegment_066_0000_1080, g32p_row03_traceSegment_066_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 2160 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2176 8 9, g32p_row03_traceSegment_066_2176_0008, g32p_row03_traceSegment_066_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 2160 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2160 16 17, g32p_row03_traceSegment_066_2160_0016, g32p_row03_traceSegment_066_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2193 8 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2201 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2193 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2193 8 9, g32p_row03_traceSegment_066_2193_0008, g32p_row03_traceSegment_066_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2210 8 9, g32p_row03_traceSegment_066_2210_0008, g32p_row03_traceSegment_066_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2193 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2193 17 17, g32p_row03_traceSegment_066_2193_0017, g32p_row03_traceSegment_066_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 2160 67 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2160 33 34, g32p_row03_traceSegment_066_2160_0033, g32p_row03_traceSegment_066_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2227 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2235 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2227 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2227 8 9, g32p_row03_traceSegment_066_2227_0008, g32p_row03_traceSegment_066_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2244 8 9, g32p_row03_traceSegment_066_2244_0008, g32p_row03_traceSegment_066_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2227 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2227 17 17, g32p_row03_traceSegment_066_2227_0017, g32p_row03_traceSegment_066_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2261 8 9, g32p_row03_traceSegment_066_2261_0008, g32p_row03_traceSegment_066_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2278 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2286 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2278 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2278 8 9, g32p_row03_traceSegment_066_2278_0008, g32p_row03_traceSegment_066_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2261 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2261 17 17, g32p_row03_traceSegment_066_2261_0017, g32p_row03_traceSegment_066_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 2227 68 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2227 34 34, g32p_row03_traceSegment_066_2227_0034, g32p_row03_traceSegment_066_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 2160 135 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2160 67 68, g32p_row03_traceSegment_066_2160_0067, g32p_row03_traceSegment_066_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 2295 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2311 8 9, g32p_row03_traceSegment_066_2311_0008, g32p_row03_traceSegment_066_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 2295 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2295 16 17, g32p_row03_traceSegment_066_2295_0016, g32p_row03_traceSegment_066_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2336 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2328 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2328 8 9, g32p_row03_traceSegment_066_2328_0008, g32p_row03_traceSegment_066_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2353 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2345 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2345 8 9, g32p_row03_traceSegment_066_2345_0008, g32p_row03_traceSegment_066_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2328 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2328 17 17, g32p_row03_traceSegment_066_2328_0017, g32p_row03_traceSegment_066_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 2295 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2295 33 34, g32p_row03_traceSegment_066_2295_0033, g32p_row03_traceSegment_066_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2362 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2362 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2362 8 9, g32p_row03_traceSegment_066_2362_0008, g32p_row03_traceSegment_066_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2379 8 9, g32p_row03_traceSegment_066_2379_0008, g32p_row03_traceSegment_066_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2362 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2362 17 17, g32p_row03_traceSegment_066_2362_0017, g32p_row03_traceSegment_066_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2396 8 9, g32p_row03_traceSegment_066_2396_0008, g32p_row03_traceSegment_066_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2413 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2421 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2413 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2413 8 9, g32p_row03_traceSegment_066_2413_0008, g32p_row03_traceSegment_066_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2396 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2396 17 17, g32p_row03_traceSegment_066_2396_0017, g32p_row03_traceSegment_066_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 2362 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2362 34 34, g32p_row03_traceSegment_066_2362_0034, g32p_row03_traceSegment_066_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 2295 135 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2295 67 68, g32p_row03_traceSegment_066_2295_0067, g32p_row03_traceSegment_066_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 2160 270 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2160 135 135, g32p_row03_traceSegment_066_2160_0135, g32p_row03_traceSegment_066_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 2430 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2446 8 9, g32p_row03_traceSegment_066_2446_0008, g32p_row03_traceSegment_066_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 2430 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2430 16 17, g32p_row03_traceSegment_066_2430_0016, g32p_row03_traceSegment_066_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2463 8 9, g32p_row03_traceSegment_066_2463_0008, g32p_row03_traceSegment_066_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2480 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2480 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2480 8 9, g32p_row03_traceSegment_066_2480_0008, g32p_row03_traceSegment_066_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2463 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2463 17 17, g32p_row03_traceSegment_066_2463_0017, g32p_row03_traceSegment_066_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 2430 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2430 33 34, g32p_row03_traceSegment_066_2430_0033, g32p_row03_traceSegment_066_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2505 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2497 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2497 8 9, g32p_row03_traceSegment_066_2497_0008, g32p_row03_traceSegment_066_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2514 8 9, g32p_row03_traceSegment_066_2514_0008, g32p_row03_traceSegment_066_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2497 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2497 17 17, g32p_row03_traceSegment_066_2497_0017, g32p_row03_traceSegment_066_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2539 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2531 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2531 8 9, g32p_row03_traceSegment_066_2531_0008, g32p_row03_traceSegment_066_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2548 8 9, g32p_row03_traceSegment_066_2548_0008, g32p_row03_traceSegment_066_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2531 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2531 17 17, g32p_row03_traceSegment_066_2531_0017, g32p_row03_traceSegment_066_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 2497 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2497 34 34, g32p_row03_traceSegment_066_2497_0034, g32p_row03_traceSegment_066_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 2430 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2430 67 68, g32p_row03_traceSegment_066_2430_0067, g32p_row03_traceSegment_066_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 2565 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2589 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2581 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2581 8 9, g32p_row03_traceSegment_066_2581_0008, g32p_row03_traceSegment_066_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 2565 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2565 16 17, g32p_row03_traceSegment_066_2565_0016, g32p_row03_traceSegment_066_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2598 8 9, g32p_row03_traceSegment_066_2598_0008, g32p_row03_traceSegment_066_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2615 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2623 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2615 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2615 8 9, g32p_row03_traceSegment_066_2615_0008, g32p_row03_traceSegment_066_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2598 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2598 17 17, g32p_row03_traceSegment_066_2598_0017, g32p_row03_traceSegment_066_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 2565 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2565 33 34, g32p_row03_traceSegment_066_2565_0033, g32p_row03_traceSegment_066_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2632 8 9, g32p_row03_traceSegment_066_2632_0008, g32p_row03_traceSegment_066_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2649 8 9, g32p_row03_traceSegment_066_2649_0008, g32p_row03_traceSegment_066_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2632 17 17, g32p_row03_traceSegment_066_2632_0017, g32p_row03_traceSegment_066_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2666 8 9, g32p_row03_traceSegment_066_2666_0008, g32p_row03_traceSegment_066_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2683 8 9, g32p_row03_traceSegment_066_2683_0008, g32p_row03_traceSegment_066_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2666 17 17, g32p_row03_traceSegment_066_2666_0017, g32p_row03_traceSegment_066_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2632 34 34, g32p_row03_traceSegment_066_2632_0034, g32p_row03_traceSegment_066_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 2565 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2565 67 68, g32p_row03_traceSegment_066_2565_0067, g32p_row03_traceSegment_066_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 2430 270 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2430 135 135, g32p_row03_traceSegment_066_2430_0135, g32p_row03_traceSegment_066_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_066 2160 540 = [0, 26] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2160 270 270, g32p_row03_traceSegment_066_2160_0270, g32p_row03_traceSegment_066_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 2700 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2716 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2716 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2716 8 9, g32p_row03_traceSegment_066_2716_0008, g32p_row03_traceSegment_066_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 2700 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2700 16 17, g32p_row03_traceSegment_066_2700_0016, g32p_row03_traceSegment_066_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2733 8 9, g32p_row03_traceSegment_066_2733_0008, g32p_row03_traceSegment_066_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2750 8 9, g32p_row03_traceSegment_066_2750_0008, g32p_row03_traceSegment_066_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2733 17 17, g32p_row03_traceSegment_066_2733_0017, g32p_row03_traceSegment_066_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 2700 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2700 33 34, g32p_row03_traceSegment_066_2700_0033, g32p_row03_traceSegment_066_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2767 8 9, g32p_row03_traceSegment_066_2767_0008, g32p_row03_traceSegment_066_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2784 8 9, g32p_row03_traceSegment_066_2784_0008, g32p_row03_traceSegment_066_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2767 17 17, g32p_row03_traceSegment_066_2767_0017, g32p_row03_traceSegment_066_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2801 8 9, g32p_row03_traceSegment_066_2801_0008, g32p_row03_traceSegment_066_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2818 8 9, g32p_row03_traceSegment_066_2818_0008, g32p_row03_traceSegment_066_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2801 17 17, g32p_row03_traceSegment_066_2801_0017, g32p_row03_traceSegment_066_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2767 34 34, g32p_row03_traceSegment_066_2767_0034, g32p_row03_traceSegment_066_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 2700 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2700 67 68, g32p_row03_traceSegment_066_2700_0067, g32p_row03_traceSegment_066_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 2835 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2851 8 9, g32p_row03_traceSegment_066_2851_0008, g32p_row03_traceSegment_066_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 2835 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2835 16 17, g32p_row03_traceSegment_066_2835_0016, g32p_row03_traceSegment_066_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2868 8 9, g32p_row03_traceSegment_066_2868_0008, g32p_row03_traceSegment_066_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2885 8 9, g32p_row03_traceSegment_066_2885_0008, g32p_row03_traceSegment_066_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2868 17 17, g32p_row03_traceSegment_066_2868_0017, g32p_row03_traceSegment_066_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 2835 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2835 33 34, g32p_row03_traceSegment_066_2835_0033, g32p_row03_traceSegment_066_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2902 8 9, g32p_row03_traceSegment_066_2902_0008, g32p_row03_traceSegment_066_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2919 8 9, g32p_row03_traceSegment_066_2919_0008, g32p_row03_traceSegment_066_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2902 17 17, g32p_row03_traceSegment_066_2902_0017, g32p_row03_traceSegment_066_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2936 8 9, g32p_row03_traceSegment_066_2936_0008, g32p_row03_traceSegment_066_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2953 8 9, g32p_row03_traceSegment_066_2953_0008, g32p_row03_traceSegment_066_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2936 17 17, g32p_row03_traceSegment_066_2936_0017, g32p_row03_traceSegment_066_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2902 34 34, g32p_row03_traceSegment_066_2902_0034, g32p_row03_traceSegment_066_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 2835 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2835 67 68, g32p_row03_traceSegment_066_2835_0067, g32p_row03_traceSegment_066_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 2700 270 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2700 135 135, g32p_row03_traceSegment_066_2700_0135, g32p_row03_traceSegment_066_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2986 8 9, g32p_row03_traceSegment_066_2986_0008, g32p_row03_traceSegment_066_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2970 16 17, g32p_row03_traceSegment_066_2970_0016, g32p_row03_traceSegment_066_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3003 8 9, g32p_row03_traceSegment_066_3003_0008, g32p_row03_traceSegment_066_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3020 8 9, g32p_row03_traceSegment_066_3020_0008, g32p_row03_traceSegment_066_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3003 17 17, g32p_row03_traceSegment_066_3003_0017, g32p_row03_traceSegment_066_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2970 33 34, g32p_row03_traceSegment_066_2970_0033, g32p_row03_traceSegment_066_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3037 8 9, g32p_row03_traceSegment_066_3037_0008, g32p_row03_traceSegment_066_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3054 8 9, g32p_row03_traceSegment_066_3054_0008, g32p_row03_traceSegment_066_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3037 17 17, g32p_row03_traceSegment_066_3037_0017, g32p_row03_traceSegment_066_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3071 8 9, g32p_row03_traceSegment_066_3071_0008, g32p_row03_traceSegment_066_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3088 8 9, g32p_row03_traceSegment_066_3088_0008, g32p_row03_traceSegment_066_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3071 17 17, g32p_row03_traceSegment_066_3071_0017, g32p_row03_traceSegment_066_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3037 34 34, g32p_row03_traceSegment_066_3037_0034, g32p_row03_traceSegment_066_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2970 67 68, g32p_row03_traceSegment_066_2970_0067, g32p_row03_traceSegment_066_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3121 8 9, g32p_row03_traceSegment_066_3121_0008, g32p_row03_traceSegment_066_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3105 16 17, g32p_row03_traceSegment_066_3105_0016, g32p_row03_traceSegment_066_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3138 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3138 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3138 8 9, g32p_row03_traceSegment_066_3138_0008, g32p_row03_traceSegment_066_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3155 8 9, g32p_row03_traceSegment_066_3155_0008, g32p_row03_traceSegment_066_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3138 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3138 17 17, g32p_row03_traceSegment_066_3138_0017, g32p_row03_traceSegment_066_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 3105 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3105 33 34, g32p_row03_traceSegment_066_3105_0033, g32p_row03_traceSegment_066_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3172 8 9, g32p_row03_traceSegment_066_3172_0008, g32p_row03_traceSegment_066_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3189 8 9, g32p_row03_traceSegment_066_3189_0008, g32p_row03_traceSegment_066_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3172 17 17, g32p_row03_traceSegment_066_3172_0017, g32p_row03_traceSegment_066_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3206 8 9, g32p_row03_traceSegment_066_3206_0008, g32p_row03_traceSegment_066_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3223 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3223 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3223 8 9, g32p_row03_traceSegment_066_3223_0008, g32p_row03_traceSegment_066_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3206 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3206 17 17, g32p_row03_traceSegment_066_3206_0017, g32p_row03_traceSegment_066_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 3172 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3172 34 34, g32p_row03_traceSegment_066_3172_0034, g32p_row03_traceSegment_066_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 3105 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3105 67 68, g32p_row03_traceSegment_066_3105_0067, g32p_row03_traceSegment_066_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 2970 270 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2970 135 135, g32p_row03_traceSegment_066_2970_0135, g32p_row03_traceSegment_066_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_066 2700 540 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2700 270 270, g32p_row03_traceSegment_066_2700_0270, g32p_row03_traceSegment_066_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_066 2160 1080 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2160 540 540, g32p_row03_traceSegment_066_2160_0540, g32p_row03_traceSegment_066_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 3240 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3256 8 9, g32p_row03_traceSegment_066_3256_0008, g32p_row03_traceSegment_066_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 3240 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3240 16 17, g32p_row03_traceSegment_066_3240_0016, g32p_row03_traceSegment_066_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3273 8 9, g32p_row03_traceSegment_066_3273_0008, g32p_row03_traceSegment_066_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3290 8 9, g32p_row03_traceSegment_066_3290_0008, g32p_row03_traceSegment_066_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3273 17 17, g32p_row03_traceSegment_066_3273_0017, g32p_row03_traceSegment_066_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 3240 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3240 33 34, g32p_row03_traceSegment_066_3240_0033, g32p_row03_traceSegment_066_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3315 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3307 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3307 8 9, g32p_row03_traceSegment_066_3307_0008, g32p_row03_traceSegment_066_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3324 8 9, g32p_row03_traceSegment_066_3324_0008, g32p_row03_traceSegment_066_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3307 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3307 17 17, g32p_row03_traceSegment_066_3307_0017, g32p_row03_traceSegment_066_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3341 8 9, g32p_row03_traceSegment_066_3341_0008, g32p_row03_traceSegment_066_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3358 8 9, g32p_row03_traceSegment_066_3358_0008, g32p_row03_traceSegment_066_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3341 17 17, g32p_row03_traceSegment_066_3341_0017, g32p_row03_traceSegment_066_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 3307 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3307 34 34, g32p_row03_traceSegment_066_3307_0034, g32p_row03_traceSegment_066_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 3240 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3240 67 68, g32p_row03_traceSegment_066_3240_0067, g32p_row03_traceSegment_066_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3391 8 9, g32p_row03_traceSegment_066_3391_0008, g32p_row03_traceSegment_066_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3375 16 17, g32p_row03_traceSegment_066_3375_0016, g32p_row03_traceSegment_066_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3408 8 9, g32p_row03_traceSegment_066_3408_0008, g32p_row03_traceSegment_066_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3425 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3433 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3425 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3425 8 9, g32p_row03_traceSegment_066_3425_0008, g32p_row03_traceSegment_066_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3408 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3408 17 17, g32p_row03_traceSegment_066_3408_0017, g32p_row03_traceSegment_066_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 3375 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3375 33 34, g32p_row03_traceSegment_066_3375_0033, g32p_row03_traceSegment_066_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3450 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3442 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3442 8 9, g32p_row03_traceSegment_066_3442_0008, g32p_row03_traceSegment_066_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3459 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3459 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3459 8 9, g32p_row03_traceSegment_066_3459_0008, g32p_row03_traceSegment_066_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3442 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3442 17 17, g32p_row03_traceSegment_066_3442_0017, g32p_row03_traceSegment_066_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3476 8 9, g32p_row03_traceSegment_066_3476_0008, g32p_row03_traceSegment_066_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3493 8 9, g32p_row03_traceSegment_066_3493_0008, g32p_row03_traceSegment_066_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3476 17 17, g32p_row03_traceSegment_066_3476_0017, g32p_row03_traceSegment_066_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 3442 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3442 34 34, g32p_row03_traceSegment_066_3442_0034, g32p_row03_traceSegment_066_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 3375 135 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3375 67 68, g32p_row03_traceSegment_066_3375_0067, g32p_row03_traceSegment_066_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 3240 270 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3240 135 135, g32p_row03_traceSegment_066_3240_0135, g32p_row03_traceSegment_066_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3534 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3526 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3526 8 9, g32p_row03_traceSegment_066_3526_0008, g32p_row03_traceSegment_066_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 3510 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3510 16 17, g32p_row03_traceSegment_066_3510_0016, g32p_row03_traceSegment_066_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3543 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3551 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3543 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3543 8 9, g32p_row03_traceSegment_066_3543_0008, g32p_row03_traceSegment_066_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3560 8 9, g32p_row03_traceSegment_066_3560_0008, g32p_row03_traceSegment_066_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3543 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3543 17 17, g32p_row03_traceSegment_066_3543_0017, g32p_row03_traceSegment_066_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 3510 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3510 33 34, g32p_row03_traceSegment_066_3510_0033, g32p_row03_traceSegment_066_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3577 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3577 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3577 8 9, g32p_row03_traceSegment_066_3577_0008, g32p_row03_traceSegment_066_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3594 8 9, g32p_row03_traceSegment_066_3594_0008, g32p_row03_traceSegment_066_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3577 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3577 17 17, g32p_row03_traceSegment_066_3577_0017, g32p_row03_traceSegment_066_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3611 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3619 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3611 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3611 8 9, g32p_row03_traceSegment_066_3611_0008, g32p_row03_traceSegment_066_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3628 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3628 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3628 8 9, g32p_row03_traceSegment_066_3628_0008, g32p_row03_traceSegment_066_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3611 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3611 17 17, g32p_row03_traceSegment_066_3611_0017, g32p_row03_traceSegment_066_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 3577 68 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3577 34 34, g32p_row03_traceSegment_066_3577_0034, g32p_row03_traceSegment_066_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 3510 135 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3510 67 68, g32p_row03_traceSegment_066_3510_0067, g32p_row03_traceSegment_066_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3661 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3669 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3661 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3661 8 9, g32p_row03_traceSegment_066_3661_0008, g32p_row03_traceSegment_066_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 3645 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3645 16 17, g32p_row03_traceSegment_066_3645_0016, g32p_row03_traceSegment_066_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3686 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3678 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3678 8 9, g32p_row03_traceSegment_066_3678_0008, g32p_row03_traceSegment_066_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3703 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3695 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3695 8 9, g32p_row03_traceSegment_066_3695_0008, g32p_row03_traceSegment_066_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3678 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3678 17 17, g32p_row03_traceSegment_066_3678_0017, g32p_row03_traceSegment_066_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 3645 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3645 33 34, g32p_row03_traceSegment_066_3645_0033, g32p_row03_traceSegment_066_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3712 8 9, g32p_row03_traceSegment_066_3712_0008, g32p_row03_traceSegment_066_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3729 8 9, g32p_row03_traceSegment_066_3729_0008, g32p_row03_traceSegment_066_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3712 17 17, g32p_row03_traceSegment_066_3712_0017, g32p_row03_traceSegment_066_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3746 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3746 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3746 8 9, g32p_row03_traceSegment_066_3746_0008, g32p_row03_traceSegment_066_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3763 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3763 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3763 8 9, g32p_row03_traceSegment_066_3763_0008, g32p_row03_traceSegment_066_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3746 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3746 17 17, g32p_row03_traceSegment_066_3746_0017, g32p_row03_traceSegment_066_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 3712 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3712 34 34, g32p_row03_traceSegment_066_3712_0034, g32p_row03_traceSegment_066_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 3645 135 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3645 67 68, g32p_row03_traceSegment_066_3645_0067, g32p_row03_traceSegment_066_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 3510 270 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3510 135 135, g32p_row03_traceSegment_066_3510_0135, g32p_row03_traceSegment_066_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_066 3240 540 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3240 270 270, g32p_row03_traceSegment_066_3240_0270, g32p_row03_traceSegment_066_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3796 8 9, g32p_row03_traceSegment_066_3796_0008, g32p_row03_traceSegment_066_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3780 16 17, g32p_row03_traceSegment_066_3780_0016, g32p_row03_traceSegment_066_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3821 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3813 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3813 8 9, g32p_row03_traceSegment_066_3813_0008, g32p_row03_traceSegment_066_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3838 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3830 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3830 8 9, g32p_row03_traceSegment_066_3830_0008, g32p_row03_traceSegment_066_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3813 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3813 17 17, g32p_row03_traceSegment_066_3813_0017, g32p_row03_traceSegment_066_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 3780 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3780 33 34, g32p_row03_traceSegment_066_3780_0033, g32p_row03_traceSegment_066_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3847 8 9, g32p_row03_traceSegment_066_3847_0008, g32p_row03_traceSegment_066_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3864 8 9, g32p_row03_traceSegment_066_3864_0008, g32p_row03_traceSegment_066_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3847 17 17, g32p_row03_traceSegment_066_3847_0017, g32p_row03_traceSegment_066_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3881 8 9, g32p_row03_traceSegment_066_3881_0008, g32p_row03_traceSegment_066_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3898 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3906 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3898 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3898 8 9, g32p_row03_traceSegment_066_3898_0008, g32p_row03_traceSegment_066_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3881 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3881 17 17, g32p_row03_traceSegment_066_3881_0017, g32p_row03_traceSegment_066_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 3847 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3847 34 34, g32p_row03_traceSegment_066_3847_0034, g32p_row03_traceSegment_066_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 3780 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3780 67 68, g32p_row03_traceSegment_066_3780_0067, g32p_row03_traceSegment_066_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3931 8 9, g32p_row03_traceSegment_066_3931_0008, g32p_row03_traceSegment_066_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3915 16 17, g32p_row03_traceSegment_066_3915_0016, g32p_row03_traceSegment_066_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3948 8 9, g32p_row03_traceSegment_066_3948_0008, g32p_row03_traceSegment_066_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3965 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3965 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3965 8 9, g32p_row03_traceSegment_066_3965_0008, g32p_row03_traceSegment_066_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3948 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3948 17 17, g32p_row03_traceSegment_066_3948_0017, g32p_row03_traceSegment_066_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 3915 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3915 33 34, g32p_row03_traceSegment_066_3915_0033, g32p_row03_traceSegment_066_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 3990 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3982 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3982 8 9, g32p_row03_traceSegment_066_3982_0008, g32p_row03_traceSegment_066_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 3999 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 3999 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3999 8 9, g32p_row03_traceSegment_066_3999_0008, g32p_row03_traceSegment_066_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 3982 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3982 17 17, g32p_row03_traceSegment_066_3982_0017, g32p_row03_traceSegment_066_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4016 8 9, g32p_row03_traceSegment_066_4016_0008, g32p_row03_traceSegment_066_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4033 8 9, g32p_row03_traceSegment_066_4033_0008, g32p_row03_traceSegment_066_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4016 17 17, g32p_row03_traceSegment_066_4016_0017, g32p_row03_traceSegment_066_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 3982 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3982 34 34, g32p_row03_traceSegment_066_3982_0034, g32p_row03_traceSegment_066_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 3915 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3915 67 68, g32p_row03_traceSegment_066_3915_0067, g32p_row03_traceSegment_066_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 3780 270 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3780 135 135, g32p_row03_traceSegment_066_3780_0135, g32p_row03_traceSegment_066_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4066 8 9, g32p_row03_traceSegment_066_4066_0008, g32p_row03_traceSegment_066_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4050 16 17, g32p_row03_traceSegment_066_4050_0016, g32p_row03_traceSegment_066_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4083 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4083 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4083 8 9, g32p_row03_traceSegment_066_4083_0008, g32p_row03_traceSegment_066_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4108 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4100 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4100 8 9, g32p_row03_traceSegment_066_4100_0008, g32p_row03_traceSegment_066_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 4083 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4083 17 17, g32p_row03_traceSegment_066_4083_0017, g32p_row03_traceSegment_066_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 4050 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4050 33 34, g32p_row03_traceSegment_066_4050_0033, g32p_row03_traceSegment_066_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4117 8 9, g32p_row03_traceSegment_066_4117_0008, g32p_row03_traceSegment_066_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4142 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4134 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4134 8 9, g32p_row03_traceSegment_066_4134_0008, g32p_row03_traceSegment_066_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 4117 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4117 17 17, g32p_row03_traceSegment_066_4117_0017, g32p_row03_traceSegment_066_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4151 8 9, g32p_row03_traceSegment_066_4151_0008, g32p_row03_traceSegment_066_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4168 8 9, g32p_row03_traceSegment_066_4168_0008, g32p_row03_traceSegment_066_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4151 17 17, g32p_row03_traceSegment_066_4151_0017, g32p_row03_traceSegment_066_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 4117 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4117 34 34, g32p_row03_traceSegment_066_4117_0034, g32p_row03_traceSegment_066_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 4050 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4050 67 68, g32p_row03_traceSegment_066_4050_0067, g32p_row03_traceSegment_066_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_066 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4201 8 9, g32p_row03_traceSegment_066_4201_0008, g32p_row03_traceSegment_066_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_066 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4185 16 17, g32p_row03_traceSegment_066_4185_0016, g32p_row03_traceSegment_066_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4218 8 9, g32p_row03_traceSegment_066_4218_0008, g32p_row03_traceSegment_066_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4235 8 9, g32p_row03_traceSegment_066_4235_0008, g32p_row03_traceSegment_066_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4218 17 17, g32p_row03_traceSegment_066_4218_0017, g32p_row03_traceSegment_066_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_066 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4185 33 34, g32p_row03_traceSegment_066_4185_0033, g32p_row03_traceSegment_066_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4252 8 9, g32p_row03_traceSegment_066_4252_0008, g32p_row03_traceSegment_066_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4269 8 9, g32p_row03_traceSegment_066_4269_0008, g32p_row03_traceSegment_066_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4252 17 17, g32p_row03_traceSegment_066_4252_0017, g32p_row03_traceSegment_066_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4286 8 9, g32p_row03_traceSegment_066_4286_0008, g32p_row03_traceSegment_066_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_066 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_066 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_066_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_066 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4303 8 9, g32p_row03_traceSegment_066_4303_0008, g32p_row03_traceSegment_066_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_066 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4286 17 17, g32p_row03_traceSegment_066_4286_0017, g32p_row03_traceSegment_066_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_066 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4252 34 34, g32p_row03_traceSegment_066_4252_0034, g32p_row03_traceSegment_066_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_066 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4185 67 68, g32p_row03_traceSegment_066_4185_0067, g32p_row03_traceSegment_066_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_066_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_066 4050 270 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 4050 135 135, g32p_row03_traceSegment_066_4050_0135, g32p_row03_traceSegment_066_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_066 3780 540 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3780 270 270, g32p_row03_traceSegment_066_3780_0270, g32p_row03_traceSegment_066_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_066_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_066 3240 1080 = [0, 33] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 3240 540 540, g32p_row03_traceSegment_066_3240_0540, g32p_row03_traceSegment_066_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_066_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_066 2160 2160 = [0, 64] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 2160 1080 1080, g32p_row03_traceSegment_066_2160_1080, g32p_row03_traceSegment_066_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_066_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_066 0 4320 = [0, 120] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_066 0 2160 2160, g32p_row03_traceSegment_066_0000_2160, g32p_row03_traceSegment_066_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 66 = [0, 120] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_066_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_069_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 0 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 16 8 9, g32p_row03_traceSegment_069_0016_0008, g32p_row03_traceSegment_069_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 0 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 0 16 17, g32p_row03_traceSegment_069_0000_0016, g32p_row03_traceSegment_069_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 33 8 9, g32p_row03_traceSegment_069_0033_0008, g32p_row03_traceSegment_069_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 58 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 50 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 50 8 9, g32p_row03_traceSegment_069_0050_0008, g32p_row03_traceSegment_069_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 33 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 33 17 17, g32p_row03_traceSegment_069_0033_0017, g32p_row03_traceSegment_069_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 0 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 0 33 34, g32p_row03_traceSegment_069_0000_0033, g32p_row03_traceSegment_069_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 67 8 9, g32p_row03_traceSegment_069_0067_0008, g32p_row03_traceSegment_069_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 84 8 9, g32p_row03_traceSegment_069_0084_0008, g32p_row03_traceSegment_069_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 67 17 17, g32p_row03_traceSegment_069_0067_0017, g32p_row03_traceSegment_069_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 109 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 101 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 101 8 9, g32p_row03_traceSegment_069_0101_0008, g32p_row03_traceSegment_069_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 118 8 9, g32p_row03_traceSegment_069_0118_0008, g32p_row03_traceSegment_069_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 101 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 101 17 17, g32p_row03_traceSegment_069_0101_0017, g32p_row03_traceSegment_069_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 67 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 67 34 34, g32p_row03_traceSegment_069_0067_0034, g32p_row03_traceSegment_069_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 0 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 0 67 68, g32p_row03_traceSegment_069_0000_0067, g32p_row03_traceSegment_069_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 151 8 9, g32p_row03_traceSegment_069_0151_0008, g32p_row03_traceSegment_069_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 135 16 17, g32p_row03_traceSegment_069_0135_0016, g32p_row03_traceSegment_069_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 168 8 9, g32p_row03_traceSegment_069_0168_0008, g32p_row03_traceSegment_069_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 185 8 9, g32p_row03_traceSegment_069_0185_0008, g32p_row03_traceSegment_069_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 168 17 17, g32p_row03_traceSegment_069_0168_0017, g32p_row03_traceSegment_069_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 135 33 34, g32p_row03_traceSegment_069_0135_0033, g32p_row03_traceSegment_069_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 202 8 9, g32p_row03_traceSegment_069_0202_0008, g32p_row03_traceSegment_069_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 219 8 9, g32p_row03_traceSegment_069_0219_0008, g32p_row03_traceSegment_069_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 202 17 17, g32p_row03_traceSegment_069_0202_0017, g32p_row03_traceSegment_069_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 236 8 9, g32p_row03_traceSegment_069_0236_0008, g32p_row03_traceSegment_069_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 253 8 9, g32p_row03_traceSegment_069_0253_0008, g32p_row03_traceSegment_069_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 236 17 17, g32p_row03_traceSegment_069_0236_0017, g32p_row03_traceSegment_069_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 202 34 34, g32p_row03_traceSegment_069_0202_0034, g32p_row03_traceSegment_069_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 135 67 68, g32p_row03_traceSegment_069_0135_0067, g32p_row03_traceSegment_069_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 0 270 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 0 135 135, g32p_row03_traceSegment_069_0000_0135, g32p_row03_traceSegment_069_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 294 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 286 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 286 8 9, g32p_row03_traceSegment_069_0286_0008, g32p_row03_traceSegment_069_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 270 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 270 16 17, g32p_row03_traceSegment_069_0270_0016, g32p_row03_traceSegment_069_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 303 8 9, g32p_row03_traceSegment_069_0303_0008, g32p_row03_traceSegment_069_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 320 8 9, g32p_row03_traceSegment_069_0320_0008, g32p_row03_traceSegment_069_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 303 17 17, g32p_row03_traceSegment_069_0303_0017, g32p_row03_traceSegment_069_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 270 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 270 33 34, g32p_row03_traceSegment_069_0270_0033, g32p_row03_traceSegment_069_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 345 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 337 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 337 8 9, g32p_row03_traceSegment_069_0337_0008, g32p_row03_traceSegment_069_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 354 8 9, g32p_row03_traceSegment_069_0354_0008, g32p_row03_traceSegment_069_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 337 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 337 17 17, g32p_row03_traceSegment_069_0337_0017, g32p_row03_traceSegment_069_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 379 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 371 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 371 8 9, g32p_row03_traceSegment_069_0371_0008, g32p_row03_traceSegment_069_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 396 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 388 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 388 8 9, g32p_row03_traceSegment_069_0388_0008, g32p_row03_traceSegment_069_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 371 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 371 17 17, g32p_row03_traceSegment_069_0371_0017, g32p_row03_traceSegment_069_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 337 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 337 34 34, g32p_row03_traceSegment_069_0337_0034, g32p_row03_traceSegment_069_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 270 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 270 67 68, g32p_row03_traceSegment_069_0270_0067, g32p_row03_traceSegment_069_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 429 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 421 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 421 8 9, g32p_row03_traceSegment_069_0421_0008, g32p_row03_traceSegment_069_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 405 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 405 16 17, g32p_row03_traceSegment_069_0405_0016, g32p_row03_traceSegment_069_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 438 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 438 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 438 8 9, g32p_row03_traceSegment_069_0438_0008, g32p_row03_traceSegment_069_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 455 8 9, g32p_row03_traceSegment_069_0455_0008, g32p_row03_traceSegment_069_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 438 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 438 17 17, g32p_row03_traceSegment_069_0438_0017, g32p_row03_traceSegment_069_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 405 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 405 33 34, g32p_row03_traceSegment_069_0405_0033, g32p_row03_traceSegment_069_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 472 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 472 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 472 8 9, g32p_row03_traceSegment_069_0472_0008, g32p_row03_traceSegment_069_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 497 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 489 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 489 8 9, g32p_row03_traceSegment_069_0489_0008, g32p_row03_traceSegment_069_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 472 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 472 17 17, g32p_row03_traceSegment_069_0472_0017, g32p_row03_traceSegment_069_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 506 8 9, g32p_row03_traceSegment_069_0506_0008, g32p_row03_traceSegment_069_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 523 8 9, g32p_row03_traceSegment_069_0523_0008, g32p_row03_traceSegment_069_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 506 17 17, g32p_row03_traceSegment_069_0506_0017, g32p_row03_traceSegment_069_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 472 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 472 34 34, g32p_row03_traceSegment_069_0472_0034, g32p_row03_traceSegment_069_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 405 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 405 67 68, g32p_row03_traceSegment_069_0405_0067, g32p_row03_traceSegment_069_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 270 270 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 270 135 135, g32p_row03_traceSegment_069_0270_0135, g32p_row03_traceSegment_069_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_069 0 540 = [11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 0 270 270, g32p_row03_traceSegment_069_0000_0270, g32p_row03_traceSegment_069_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 540 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 556 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 556 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 556 8 9, g32p_row03_traceSegment_069_0556_0008, g32p_row03_traceSegment_069_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 540 33 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 540 16 17, g32p_row03_traceSegment_069_0540_0016, g32p_row03_traceSegment_069_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 573 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 581 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 573 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 573 8 9, g32p_row03_traceSegment_069_0573_0008, g32p_row03_traceSegment_069_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 590 8 9, g32p_row03_traceSegment_069_0590_0008, g32p_row03_traceSegment_069_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 573 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 573 17 17, g32p_row03_traceSegment_069_0573_0017, g32p_row03_traceSegment_069_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 540 67 = [3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 540 33 34, g32p_row03_traceSegment_069_0540_0033, g32p_row03_traceSegment_069_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 607 8 9, g32p_row03_traceSegment_069_0607_0008, g32p_row03_traceSegment_069_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 624 8 9, g32p_row03_traceSegment_069_0624_0008, g32p_row03_traceSegment_069_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 607 17 17, g32p_row03_traceSegment_069_0607_0017, g32p_row03_traceSegment_069_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 641 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 649 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 641 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 641 8 9, g32p_row03_traceSegment_069_0641_0008, g32p_row03_traceSegment_069_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 658 8 9, g32p_row03_traceSegment_069_0658_0008, g32p_row03_traceSegment_069_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 641 34 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 641 17 17, g32p_row03_traceSegment_069_0641_0017, g32p_row03_traceSegment_069_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 607 68 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 607 34 34, g32p_row03_traceSegment_069_0607_0034, g32p_row03_traceSegment_069_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 540 135 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 540 67 68, g32p_row03_traceSegment_069_0540_0067, g32p_row03_traceSegment_069_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 691 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 691 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 691 8 9, g32p_row03_traceSegment_069_0691_0008, g32p_row03_traceSegment_069_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 675 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 675 16 17, g32p_row03_traceSegment_069_0675_0016, g32p_row03_traceSegment_069_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 708 8 9, g32p_row03_traceSegment_069_0708_0008, g32p_row03_traceSegment_069_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 725 8 9, g32p_row03_traceSegment_069_0725_0008, g32p_row03_traceSegment_069_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 708 17 17, g32p_row03_traceSegment_069_0708_0017, g32p_row03_traceSegment_069_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 675 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 675 33 34, g32p_row03_traceSegment_069_0675_0033, g32p_row03_traceSegment_069_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 742 8 9, g32p_row03_traceSegment_069_0742_0008, g32p_row03_traceSegment_069_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 767 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 759 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 759 8 9, g32p_row03_traceSegment_069_0759_0008, g32p_row03_traceSegment_069_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 742 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 742 17 17, g32p_row03_traceSegment_069_0742_0017, g32p_row03_traceSegment_069_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 776 8 9, g32p_row03_traceSegment_069_0776_0008, g32p_row03_traceSegment_069_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 793 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 793 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 793 8 9, g32p_row03_traceSegment_069_0793_0008, g32p_row03_traceSegment_069_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 776 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 776 17 17, g32p_row03_traceSegment_069_0776_0017, g32p_row03_traceSegment_069_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 742 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 742 34 34, g32p_row03_traceSegment_069_0742_0034, g32p_row03_traceSegment_069_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 675 135 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 675 67 68, g32p_row03_traceSegment_069_0675_0067, g32p_row03_traceSegment_069_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 540 270 = [6, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 540 135 135, g32p_row03_traceSegment_069_0540_0135, g32p_row03_traceSegment_069_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 810 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 826 8 9, g32p_row03_traceSegment_069_0826_0008, g32p_row03_traceSegment_069_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 810 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 810 16 17, g32p_row03_traceSegment_069_0810_0016, g32p_row03_traceSegment_069_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 851 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 843 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 843 8 9, g32p_row03_traceSegment_069_0843_0008, g32p_row03_traceSegment_069_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 868 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 860 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 860 8 9, g32p_row03_traceSegment_069_0860_0008, g32p_row03_traceSegment_069_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 843 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 843 17 17, g32p_row03_traceSegment_069_0843_0017, g32p_row03_traceSegment_069_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 810 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 810 33 34, g32p_row03_traceSegment_069_0810_0033, g32p_row03_traceSegment_069_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 877 8 9, g32p_row03_traceSegment_069_0877_0008, g32p_row03_traceSegment_069_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 902 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 894 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 894 8 9, g32p_row03_traceSegment_069_0894_0008, g32p_row03_traceSegment_069_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 877 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 877 17 17, g32p_row03_traceSegment_069_0877_0017, g32p_row03_traceSegment_069_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 911 8 9, g32p_row03_traceSegment_069_0911_0008, g32p_row03_traceSegment_069_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 928 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 936 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 928 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 928 8 9, g32p_row03_traceSegment_069_0928_0008, g32p_row03_traceSegment_069_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 911 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 911 17 17, g32p_row03_traceSegment_069_0911_0017, g32p_row03_traceSegment_069_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 877 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 877 34 34, g32p_row03_traceSegment_069_0877_0034, g32p_row03_traceSegment_069_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 810 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 810 67 68, g32p_row03_traceSegment_069_0810_0067, g32p_row03_traceSegment_069_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 945 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 961 8 9, g32p_row03_traceSegment_069_0961_0008, g32p_row03_traceSegment_069_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 945 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 945 16 17, g32p_row03_traceSegment_069_0945_0016, g32p_row03_traceSegment_069_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 978 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 978 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 978 8 9, g32p_row03_traceSegment_069_0978_0008, g32p_row03_traceSegment_069_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 995 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1003 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 995 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 995 8 9, g32p_row03_traceSegment_069_0995_0008, g32p_row03_traceSegment_069_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 978 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 978 17 17, g32p_row03_traceSegment_069_0978_0017, g32p_row03_traceSegment_069_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 945 67 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 945 33 34, g32p_row03_traceSegment_069_0945_0033, g32p_row03_traceSegment_069_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1012 8 9, g32p_row03_traceSegment_069_1012_0008, g32p_row03_traceSegment_069_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1029 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1029 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1029 8 9, g32p_row03_traceSegment_069_1029_0008, g32p_row03_traceSegment_069_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1012 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1012 17 17, g32p_row03_traceSegment_069_1012_0017, g32p_row03_traceSegment_069_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1054 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1046 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1046 8 9, g32p_row03_traceSegment_069_1046_0008, g32p_row03_traceSegment_069_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1063 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1063 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1063 8 9, g32p_row03_traceSegment_069_1063_0008, g32p_row03_traceSegment_069_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1046 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1046 17 17, g32p_row03_traceSegment_069_1046_0017, g32p_row03_traceSegment_069_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 1012 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1012 34 34, g32p_row03_traceSegment_069_1012_0034, g32p_row03_traceSegment_069_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 945 135 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 945 67 68, g32p_row03_traceSegment_069_0945_0067, g32p_row03_traceSegment_069_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 810 270 = [13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 810 135 135, g32p_row03_traceSegment_069_0810_0135, g32p_row03_traceSegment_069_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_069 540 540 = [19, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 540 270 270, g32p_row03_traceSegment_069_0540_0270, g32p_row03_traceSegment_069_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_069 0 1080 = [30, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 0 540 540, g32p_row03_traceSegment_069_0000_0540, g32p_row03_traceSegment_069_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 1080 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1096 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1104 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1096 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1096 8 9, g32p_row03_traceSegment_069_1096_0008, g32p_row03_traceSegment_069_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 1080 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1080 16 17, g32p_row03_traceSegment_069_1080_0016, g32p_row03_traceSegment_069_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1121 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1113 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1113 8 9, g32p_row03_traceSegment_069_1113_0008, g32p_row03_traceSegment_069_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1130 8 9, g32p_row03_traceSegment_069_1130_0008, g32p_row03_traceSegment_069_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1113 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1113 17 17, g32p_row03_traceSegment_069_1113_0017, g32p_row03_traceSegment_069_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 1080 67 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1080 33 34, g32p_row03_traceSegment_069_1080_0033, g32p_row03_traceSegment_069_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1147 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1147 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1147 8 9, g32p_row03_traceSegment_069_1147_0008, g32p_row03_traceSegment_069_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1164 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1172 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1164 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1164 8 9, g32p_row03_traceSegment_069_1164_0008, g32p_row03_traceSegment_069_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1147 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1147 17 17, g32p_row03_traceSegment_069_1147_0017, g32p_row03_traceSegment_069_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1189 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1181 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1181 8 9, g32p_row03_traceSegment_069_1181_0008, g32p_row03_traceSegment_069_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1198 8 9, g32p_row03_traceSegment_069_1198_0008, g32p_row03_traceSegment_069_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1181 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1181 17 17, g32p_row03_traceSegment_069_1181_0017, g32p_row03_traceSegment_069_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 1147 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1147 34 34, g32p_row03_traceSegment_069_1147_0034, g32p_row03_traceSegment_069_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 1080 135 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1080 67 68, g32p_row03_traceSegment_069_1080_0067, g32p_row03_traceSegment_069_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 1215 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1231 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1231 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1231 8 9, g32p_row03_traceSegment_069_1231_0008, g32p_row03_traceSegment_069_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 1215 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1215 16 17, g32p_row03_traceSegment_069_1215_0016, g32p_row03_traceSegment_069_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1248 8 9, g32p_row03_traceSegment_069_1248_0008, g32p_row03_traceSegment_069_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1265 8 9, g32p_row03_traceSegment_069_1265_0008, g32p_row03_traceSegment_069_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1248 17 17, g32p_row03_traceSegment_069_1248_0017, g32p_row03_traceSegment_069_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 1215 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1215 33 34, g32p_row03_traceSegment_069_1215_0033, g32p_row03_traceSegment_069_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1282 8 9, g32p_row03_traceSegment_069_1282_0008, g32p_row03_traceSegment_069_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1299 8 9, g32p_row03_traceSegment_069_1299_0008, g32p_row03_traceSegment_069_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1282 17 17, g32p_row03_traceSegment_069_1282_0017, g32p_row03_traceSegment_069_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1316 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1316 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1316 8 9, g32p_row03_traceSegment_069_1316_0008, g32p_row03_traceSegment_069_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1333 8 9, g32p_row03_traceSegment_069_1333_0008, g32p_row03_traceSegment_069_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1316 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1316 17 17, g32p_row03_traceSegment_069_1316_0017, g32p_row03_traceSegment_069_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 1282 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1282 34 34, g32p_row03_traceSegment_069_1282_0034, g32p_row03_traceSegment_069_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 1215 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1215 67 68, g32p_row03_traceSegment_069_1215_0067, g32p_row03_traceSegment_069_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 1080 270 = [11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1080 135 135, g32p_row03_traceSegment_069_1080_0135, g32p_row03_traceSegment_069_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1374 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1366 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1366 8 9, g32p_row03_traceSegment_069_1366_0008, g32p_row03_traceSegment_069_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 1350 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1350 16 17, g32p_row03_traceSegment_069_1350_0016, g32p_row03_traceSegment_069_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1383 8 9, g32p_row03_traceSegment_069_1383_0008, g32p_row03_traceSegment_069_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1400 8 9, g32p_row03_traceSegment_069_1400_0008, g32p_row03_traceSegment_069_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1383 17 17, g32p_row03_traceSegment_069_1383_0017, g32p_row03_traceSegment_069_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 1350 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1350 33 34, g32p_row03_traceSegment_069_1350_0033, g32p_row03_traceSegment_069_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1417 8 9, g32p_row03_traceSegment_069_1417_0008, g32p_row03_traceSegment_069_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1434 8 9, g32p_row03_traceSegment_069_1434_0008, g32p_row03_traceSegment_069_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1417 17 17, g32p_row03_traceSegment_069_1417_0017, g32p_row03_traceSegment_069_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1451 8 9, g32p_row03_traceSegment_069_1451_0008, g32p_row03_traceSegment_069_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1468 8 9, g32p_row03_traceSegment_069_1468_0008, g32p_row03_traceSegment_069_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1451 17 17, g32p_row03_traceSegment_069_1451_0017, g32p_row03_traceSegment_069_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1417 34 34, g32p_row03_traceSegment_069_1417_0034, g32p_row03_traceSegment_069_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 1350 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1350 67 68, g32p_row03_traceSegment_069_1350_0067, g32p_row03_traceSegment_069_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 1485 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1509 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1501 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1501 8 9, g32p_row03_traceSegment_069_1501_0008, g32p_row03_traceSegment_069_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 1485 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1485 16 17, g32p_row03_traceSegment_069_1485_0016, g32p_row03_traceSegment_069_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1518 8 9, g32p_row03_traceSegment_069_1518_0008, g32p_row03_traceSegment_069_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1535 8 9, g32p_row03_traceSegment_069_1535_0008, g32p_row03_traceSegment_069_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1518 17 17, g32p_row03_traceSegment_069_1518_0017, g32p_row03_traceSegment_069_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 1485 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1485 33 34, g32p_row03_traceSegment_069_1485_0033, g32p_row03_traceSegment_069_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1552 8 9, g32p_row03_traceSegment_069_1552_0008, g32p_row03_traceSegment_069_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1569 8 9, g32p_row03_traceSegment_069_1569_0008, g32p_row03_traceSegment_069_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1552 17 17, g32p_row03_traceSegment_069_1552_0017, g32p_row03_traceSegment_069_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1586 8 9, g32p_row03_traceSegment_069_1586_0008, g32p_row03_traceSegment_069_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1603 8 9, g32p_row03_traceSegment_069_1603_0008, g32p_row03_traceSegment_069_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1586 17 17, g32p_row03_traceSegment_069_1586_0017, g32p_row03_traceSegment_069_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1552 34 34, g32p_row03_traceSegment_069_1552_0034, g32p_row03_traceSegment_069_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 1485 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1485 67 68, g32p_row03_traceSegment_069_1485_0067, g32p_row03_traceSegment_069_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 1350 270 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1350 135 135, g32p_row03_traceSegment_069_1350_0135, g32p_row03_traceSegment_069_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_069 1080 540 = [16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1080 270 270, g32p_row03_traceSegment_069_1080_0270, g32p_row03_traceSegment_069_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1636 8 9, g32p_row03_traceSegment_069_1636_0008, g32p_row03_traceSegment_069_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1620 16 17, g32p_row03_traceSegment_069_1620_0016, g32p_row03_traceSegment_069_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1653 8 9, g32p_row03_traceSegment_069_1653_0008, g32p_row03_traceSegment_069_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1670 8 9, g32p_row03_traceSegment_069_1670_0008, g32p_row03_traceSegment_069_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1653 17 17, g32p_row03_traceSegment_069_1653_0017, g32p_row03_traceSegment_069_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1620 33 34, g32p_row03_traceSegment_069_1620_0033, g32p_row03_traceSegment_069_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1687 8 9, g32p_row03_traceSegment_069_1687_0008, g32p_row03_traceSegment_069_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1712 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1704 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1704 8 9, g32p_row03_traceSegment_069_1704_0008, g32p_row03_traceSegment_069_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1687 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1687 17 17, g32p_row03_traceSegment_069_1687_0017, g32p_row03_traceSegment_069_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1721 8 9, g32p_row03_traceSegment_069_1721_0008, g32p_row03_traceSegment_069_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1738 8 9, g32p_row03_traceSegment_069_1738_0008, g32p_row03_traceSegment_069_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1721 17 17, g32p_row03_traceSegment_069_1721_0017, g32p_row03_traceSegment_069_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 1687 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1687 34 34, g32p_row03_traceSegment_069_1687_0034, g32p_row03_traceSegment_069_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 1620 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1620 67 68, g32p_row03_traceSegment_069_1620_0067, g32p_row03_traceSegment_069_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1771 8 9, g32p_row03_traceSegment_069_1771_0008, g32p_row03_traceSegment_069_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1755 16 17, g32p_row03_traceSegment_069_1755_0016, g32p_row03_traceSegment_069_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1788 8 9, g32p_row03_traceSegment_069_1788_0008, g32p_row03_traceSegment_069_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1805 8 9, g32p_row03_traceSegment_069_1805_0008, g32p_row03_traceSegment_069_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1788 17 17, g32p_row03_traceSegment_069_1788_0017, g32p_row03_traceSegment_069_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1755 33 34, g32p_row03_traceSegment_069_1755_0033, g32p_row03_traceSegment_069_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1822 8 9, g32p_row03_traceSegment_069_1822_0008, g32p_row03_traceSegment_069_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1847 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1839 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1839 8 9, g32p_row03_traceSegment_069_1839_0008, g32p_row03_traceSegment_069_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1822 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1822 17 17, g32p_row03_traceSegment_069_1822_0017, g32p_row03_traceSegment_069_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1864 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1856 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1856 8 9, g32p_row03_traceSegment_069_1856_0008, g32p_row03_traceSegment_069_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1873 8 9, g32p_row03_traceSegment_069_1873_0008, g32p_row03_traceSegment_069_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1856 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1856 17 17, g32p_row03_traceSegment_069_1856_0017, g32p_row03_traceSegment_069_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 1822 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1822 34 34, g32p_row03_traceSegment_069_1822_0034, g32p_row03_traceSegment_069_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 1755 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1755 67 68, g32p_row03_traceSegment_069_1755_0067, g32p_row03_traceSegment_069_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 1620 270 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1620 135 135, g32p_row03_traceSegment_069_1620_0135, g32p_row03_traceSegment_069_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1906 8 9, g32p_row03_traceSegment_069_1906_0008, g32p_row03_traceSegment_069_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1890 16 17, g32p_row03_traceSegment_069_1890_0016, g32p_row03_traceSegment_069_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1923 8 9, g32p_row03_traceSegment_069_1923_0008, g32p_row03_traceSegment_069_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1948 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1940 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1940 8 9, g32p_row03_traceSegment_069_1940_0008, g32p_row03_traceSegment_069_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1923 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1923 17 17, g32p_row03_traceSegment_069_1923_0017, g32p_row03_traceSegment_069_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 1890 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1890 33 34, g32p_row03_traceSegment_069_1890_0033, g32p_row03_traceSegment_069_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1957 8 9, g32p_row03_traceSegment_069_1957_0008, g32p_row03_traceSegment_069_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1974 8 9, g32p_row03_traceSegment_069_1974_0008, g32p_row03_traceSegment_069_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1957 17 17, g32p_row03_traceSegment_069_1957_0017, g32p_row03_traceSegment_069_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1991 8 9, g32p_row03_traceSegment_069_1991_0008, g32p_row03_traceSegment_069_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2008 8 9, g32p_row03_traceSegment_069_2008_0008, g32p_row03_traceSegment_069_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1991 17 17, g32p_row03_traceSegment_069_1991_0017, g32p_row03_traceSegment_069_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1957 34 34, g32p_row03_traceSegment_069_1957_0034, g32p_row03_traceSegment_069_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 1890 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1890 67 68, g32p_row03_traceSegment_069_1890_0067, g32p_row03_traceSegment_069_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 2025 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2041 8 9, g32p_row03_traceSegment_069_2041_0008, g32p_row03_traceSegment_069_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 2025 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2025 16 17, g32p_row03_traceSegment_069_2025_0016, g32p_row03_traceSegment_069_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2066 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2058 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2058 8 9, g32p_row03_traceSegment_069_2058_0008, g32p_row03_traceSegment_069_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2075 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2075 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2075 8 9, g32p_row03_traceSegment_069_2075_0008, g32p_row03_traceSegment_069_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2058 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2058 17 17, g32p_row03_traceSegment_069_2058_0017, g32p_row03_traceSegment_069_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 2025 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2025 33 34, g32p_row03_traceSegment_069_2025_0033, g32p_row03_traceSegment_069_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2092 8 9, g32p_row03_traceSegment_069_2092_0008, g32p_row03_traceSegment_069_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2117 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2109 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2109 8 9, g32p_row03_traceSegment_069_2109_0008, g32p_row03_traceSegment_069_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2092 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2092 17 17, g32p_row03_traceSegment_069_2092_0017, g32p_row03_traceSegment_069_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2126 8 9, g32p_row03_traceSegment_069_2126_0008, g32p_row03_traceSegment_069_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2143 8 9, g32p_row03_traceSegment_069_2143_0008, g32p_row03_traceSegment_069_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2126 17 17, g32p_row03_traceSegment_069_2126_0017, g32p_row03_traceSegment_069_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 2092 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2092 34 34, g32p_row03_traceSegment_069_2092_0034, g32p_row03_traceSegment_069_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 2025 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2025 67 68, g32p_row03_traceSegment_069_2025_0067, g32p_row03_traceSegment_069_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 1890 270 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1890 135 135, g32p_row03_traceSegment_069_1890_0135, g32p_row03_traceSegment_069_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_069 1620 540 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1620 270 270, g32p_row03_traceSegment_069_1620_0270, g32p_row03_traceSegment_069_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_069_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_069 1080 1080 = [24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 1080 540 540, g32p_row03_traceSegment_069_1080_0540, g32p_row03_traceSegment_069_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_069 0 2160 = [54, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 0 1080 1080, g32p_row03_traceSegment_069_0000_1080, g32p_row03_traceSegment_069_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2176 8 9, g32p_row03_traceSegment_069_2176_0008, g32p_row03_traceSegment_069_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2160 16 17, g32p_row03_traceSegment_069_2160_0016, g32p_row03_traceSegment_069_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2193 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2193 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2193 8 9, g32p_row03_traceSegment_069_2193_0008, g32p_row03_traceSegment_069_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2218 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2210 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2210 8 9, g32p_row03_traceSegment_069_2210_0008, g32p_row03_traceSegment_069_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2193 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2193 17 17, g32p_row03_traceSegment_069_2193_0017, g32p_row03_traceSegment_069_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 2160 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2160 33 34, g32p_row03_traceSegment_069_2160_0033, g32p_row03_traceSegment_069_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2235 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2227 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2227 8 9, g32p_row03_traceSegment_069_2227_0008, g32p_row03_traceSegment_069_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2244 8 9, g32p_row03_traceSegment_069_2244_0008, g32p_row03_traceSegment_069_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2227 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2227 17 17, g32p_row03_traceSegment_069_2227_0017, g32p_row03_traceSegment_069_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2261 8 9, g32p_row03_traceSegment_069_2261_0008, g32p_row03_traceSegment_069_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2286 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2278 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2278 8 9, g32p_row03_traceSegment_069_2278_0008, g32p_row03_traceSegment_069_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2261 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2261 17 17, g32p_row03_traceSegment_069_2261_0017, g32p_row03_traceSegment_069_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 2227 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2227 34 34, g32p_row03_traceSegment_069_2227_0034, g32p_row03_traceSegment_069_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 2160 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2160 67 68, g32p_row03_traceSegment_069_2160_0067, g32p_row03_traceSegment_069_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 2295 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2311 8 9, g32p_row03_traceSegment_069_2311_0008, g32p_row03_traceSegment_069_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 2295 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2295 16 17, g32p_row03_traceSegment_069_2295_0016, g32p_row03_traceSegment_069_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2328 8 9, g32p_row03_traceSegment_069_2328_0008, g32p_row03_traceSegment_069_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2345 8 9, g32p_row03_traceSegment_069_2345_0008, g32p_row03_traceSegment_069_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2328 17 17, g32p_row03_traceSegment_069_2328_0017, g32p_row03_traceSegment_069_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 2295 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2295 33 34, g32p_row03_traceSegment_069_2295_0033, g32p_row03_traceSegment_069_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2362 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2370 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2362 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2362 8 9, g32p_row03_traceSegment_069_2362_0008, g32p_row03_traceSegment_069_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2379 8 9, g32p_row03_traceSegment_069_2379_0008, g32p_row03_traceSegment_069_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2362 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2362 17 17, g32p_row03_traceSegment_069_2362_0017, g32p_row03_traceSegment_069_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2396 8 9, g32p_row03_traceSegment_069_2396_0008, g32p_row03_traceSegment_069_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2413 8 9, g32p_row03_traceSegment_069_2413_0008, g32p_row03_traceSegment_069_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2396 17 17, g32p_row03_traceSegment_069_2396_0017, g32p_row03_traceSegment_069_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 2362 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2362 34 34, g32p_row03_traceSegment_069_2362_0034, g32p_row03_traceSegment_069_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 2295 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2295 67 68, g32p_row03_traceSegment_069_2295_0067, g32p_row03_traceSegment_069_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 2160 270 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2160 135 135, g32p_row03_traceSegment_069_2160_0135, g32p_row03_traceSegment_069_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 2430 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2446 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2446 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2446 8 9, g32p_row03_traceSegment_069_2446_0008, g32p_row03_traceSegment_069_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 2430 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2430 16 17, g32p_row03_traceSegment_069_2430_0016, g32p_row03_traceSegment_069_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2463 8 9, g32p_row03_traceSegment_069_2463_0008, g32p_row03_traceSegment_069_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2488 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2480 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2480 8 9, g32p_row03_traceSegment_069_2480_0008, g32p_row03_traceSegment_069_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2463 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2463 17 17, g32p_row03_traceSegment_069_2463_0017, g32p_row03_traceSegment_069_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 2430 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2430 33 34, g32p_row03_traceSegment_069_2430_0033, g32p_row03_traceSegment_069_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2497 8 9, g32p_row03_traceSegment_069_2497_0008, g32p_row03_traceSegment_069_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2514 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2514 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2514 8 9, g32p_row03_traceSegment_069_2514_0008, g32p_row03_traceSegment_069_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2497 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2497 17 17, g32p_row03_traceSegment_069_2497_0017, g32p_row03_traceSegment_069_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2531 8 9, g32p_row03_traceSegment_069_2531_0008, g32p_row03_traceSegment_069_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2548 8 9, g32p_row03_traceSegment_069_2548_0008, g32p_row03_traceSegment_069_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2531 17 17, g32p_row03_traceSegment_069_2531_0017, g32p_row03_traceSegment_069_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 2497 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2497 34 34, g32p_row03_traceSegment_069_2497_0034, g32p_row03_traceSegment_069_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 2430 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2430 67 68, g32p_row03_traceSegment_069_2430_0067, g32p_row03_traceSegment_069_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2581 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2581 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2581 8 9, g32p_row03_traceSegment_069_2581_0008, g32p_row03_traceSegment_069_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 2565 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2565 16 17, g32p_row03_traceSegment_069_2565_0016, g32p_row03_traceSegment_069_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2598 8 9, g32p_row03_traceSegment_069_2598_0008, g32p_row03_traceSegment_069_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2623 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2615 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2615 8 9, g32p_row03_traceSegment_069_2615_0008, g32p_row03_traceSegment_069_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2598 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2598 17 17, g32p_row03_traceSegment_069_2598_0017, g32p_row03_traceSegment_069_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 2565 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2565 33 34, g32p_row03_traceSegment_069_2565_0033, g32p_row03_traceSegment_069_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2632 8 9, g32p_row03_traceSegment_069_2632_0008, g32p_row03_traceSegment_069_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2649 8 9, g32p_row03_traceSegment_069_2649_0008, g32p_row03_traceSegment_069_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2632 17 17, g32p_row03_traceSegment_069_2632_0017, g32p_row03_traceSegment_069_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2666 8 9, g32p_row03_traceSegment_069_2666_0008, g32p_row03_traceSegment_069_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2683 8 9, g32p_row03_traceSegment_069_2683_0008, g32p_row03_traceSegment_069_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2666 17 17, g32p_row03_traceSegment_069_2666_0017, g32p_row03_traceSegment_069_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2632 34 34, g32p_row03_traceSegment_069_2632_0034, g32p_row03_traceSegment_069_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 2565 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2565 67 68, g32p_row03_traceSegment_069_2565_0067, g32p_row03_traceSegment_069_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 2430 270 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2430 135 135, g32p_row03_traceSegment_069_2430_0135, g32p_row03_traceSegment_069_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_069 2160 540 = [14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2160 270 270, g32p_row03_traceSegment_069_2160_0270, g32p_row03_traceSegment_069_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 2700 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2716 8 9, g32p_row03_traceSegment_069_2716_0008, g32p_row03_traceSegment_069_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 2700 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2700 16 17, g32p_row03_traceSegment_069_2700_0016, g32p_row03_traceSegment_069_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2733 8 9, g32p_row03_traceSegment_069_2733_0008, g32p_row03_traceSegment_069_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2750 8 9, g32p_row03_traceSegment_069_2750_0008, g32p_row03_traceSegment_069_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2733 17 17, g32p_row03_traceSegment_069_2733_0017, g32p_row03_traceSegment_069_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 2700 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2700 33 34, g32p_row03_traceSegment_069_2700_0033, g32p_row03_traceSegment_069_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2767 8 9, g32p_row03_traceSegment_069_2767_0008, g32p_row03_traceSegment_069_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2784 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2784 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2784 8 9, g32p_row03_traceSegment_069_2784_0008, g32p_row03_traceSegment_069_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2767 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2767 17 17, g32p_row03_traceSegment_069_2767_0017, g32p_row03_traceSegment_069_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2801 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2801 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2801 8 9, g32p_row03_traceSegment_069_2801_0008, g32p_row03_traceSegment_069_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2818 8 9, g32p_row03_traceSegment_069_2818_0008, g32p_row03_traceSegment_069_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2801 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2801 17 17, g32p_row03_traceSegment_069_2801_0017, g32p_row03_traceSegment_069_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 2767 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2767 34 34, g32p_row03_traceSegment_069_2767_0034, g32p_row03_traceSegment_069_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 2700 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2700 67 68, g32p_row03_traceSegment_069_2700_0067, g32p_row03_traceSegment_069_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 2835 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2851 8 9, g32p_row03_traceSegment_069_2851_0008, g32p_row03_traceSegment_069_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 2835 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2835 16 17, g32p_row03_traceSegment_069_2835_0016, g32p_row03_traceSegment_069_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2868 8 9, g32p_row03_traceSegment_069_2868_0008, g32p_row03_traceSegment_069_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2885 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2885 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2885 8 9, g32p_row03_traceSegment_069_2885_0008, g32p_row03_traceSegment_069_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2868 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2868 17 17, g32p_row03_traceSegment_069_2868_0017, g32p_row03_traceSegment_069_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 2835 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2835 33 34, g32p_row03_traceSegment_069_2835_0033, g32p_row03_traceSegment_069_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2902 8 9, g32p_row03_traceSegment_069_2902_0008, g32p_row03_traceSegment_069_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2919 8 9, g32p_row03_traceSegment_069_2919_0008, g32p_row03_traceSegment_069_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2902 17 17, g32p_row03_traceSegment_069_2902_0017, g32p_row03_traceSegment_069_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2936 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2936 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2936 8 9, g32p_row03_traceSegment_069_2936_0008, g32p_row03_traceSegment_069_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2953 8 9, g32p_row03_traceSegment_069_2953_0008, g32p_row03_traceSegment_069_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 2936 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2936 17 17, g32p_row03_traceSegment_069_2936_0017, g32p_row03_traceSegment_069_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 2902 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2902 34 34, g32p_row03_traceSegment_069_2902_0034, g32p_row03_traceSegment_069_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 2835 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2835 67 68, g32p_row03_traceSegment_069_2835_0067, g32p_row03_traceSegment_069_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 2700 270 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2700 135 135, g32p_row03_traceSegment_069_2700_0135, g32p_row03_traceSegment_069_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 2970 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2986 8 9, g32p_row03_traceSegment_069_2986_0008, g32p_row03_traceSegment_069_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 2970 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2970 16 17, g32p_row03_traceSegment_069_2970_0016, g32p_row03_traceSegment_069_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3003 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3011 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3003 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3003 8 9, g32p_row03_traceSegment_069_3003_0008, g32p_row03_traceSegment_069_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3020 8 9, g32p_row03_traceSegment_069_3020_0008, g32p_row03_traceSegment_069_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3003 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3003 17 17, g32p_row03_traceSegment_069_3003_0017, g32p_row03_traceSegment_069_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 2970 67 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2970 33 34, g32p_row03_traceSegment_069_2970_0033, g32p_row03_traceSegment_069_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3037 8 9, g32p_row03_traceSegment_069_3037_0008, g32p_row03_traceSegment_069_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3054 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3062 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3054 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3054 8 9, g32p_row03_traceSegment_069_3054_0008, g32p_row03_traceSegment_069_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3037 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3037 17 17, g32p_row03_traceSegment_069_3037_0017, g32p_row03_traceSegment_069_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3071 8 9, g32p_row03_traceSegment_069_3071_0008, g32p_row03_traceSegment_069_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3088 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3088 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3088 8 9, g32p_row03_traceSegment_069_3088_0008, g32p_row03_traceSegment_069_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3071 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3071 17 17, g32p_row03_traceSegment_069_3071_0017, g32p_row03_traceSegment_069_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 3037 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3037 34 34, g32p_row03_traceSegment_069_3037_0034, g32p_row03_traceSegment_069_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 2970 135 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2970 67 68, g32p_row03_traceSegment_069_2970_0067, g32p_row03_traceSegment_069_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3121 8 9, g32p_row03_traceSegment_069_3121_0008, g32p_row03_traceSegment_069_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3105 16 17, g32p_row03_traceSegment_069_3105_0016, g32p_row03_traceSegment_069_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3138 8 9, g32p_row03_traceSegment_069_3138_0008, g32p_row03_traceSegment_069_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3155 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3163 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3155 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3155 8 9, g32p_row03_traceSegment_069_3155_0008, g32p_row03_traceSegment_069_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3138 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3138 17 17, g32p_row03_traceSegment_069_3138_0017, g32p_row03_traceSegment_069_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 3105 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3105 33 34, g32p_row03_traceSegment_069_3105_0033, g32p_row03_traceSegment_069_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3172 8 9, g32p_row03_traceSegment_069_3172_0008, g32p_row03_traceSegment_069_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3189 8 9, g32p_row03_traceSegment_069_3189_0008, g32p_row03_traceSegment_069_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3172 17 17, g32p_row03_traceSegment_069_3172_0017, g32p_row03_traceSegment_069_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3206 8 9, g32p_row03_traceSegment_069_3206_0008, g32p_row03_traceSegment_069_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3223 8 9, g32p_row03_traceSegment_069_3223_0008, g32p_row03_traceSegment_069_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3206 17 17, g32p_row03_traceSegment_069_3206_0017, g32p_row03_traceSegment_069_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3172 34 34, g32p_row03_traceSegment_069_3172_0034, g32p_row03_traceSegment_069_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 3105 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3105 67 68, g32p_row03_traceSegment_069_3105_0067, g32p_row03_traceSegment_069_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 2970 270 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2970 135 135, g32p_row03_traceSegment_069_2970_0135, g32p_row03_traceSegment_069_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_069 2700 540 = [6, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2700 270 270, g32p_row03_traceSegment_069_2700_0270, g32p_row03_traceSegment_069_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_069 2160 1080 = [20, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2160 540 540, g32p_row03_traceSegment_069_2160_0540, g32p_row03_traceSegment_069_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 3240 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3256 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3256 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3256 8 9, g32p_row03_traceSegment_069_3256_0008, g32p_row03_traceSegment_069_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 3240 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3240 16 17, g32p_row03_traceSegment_069_3240_0016, g32p_row03_traceSegment_069_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3273 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3281 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3273 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3273 8 9, g32p_row03_traceSegment_069_3273_0008, g32p_row03_traceSegment_069_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3290 8 9, g32p_row03_traceSegment_069_3290_0008, g32p_row03_traceSegment_069_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3273 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3273 17 17, g32p_row03_traceSegment_069_3273_0017, g32p_row03_traceSegment_069_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 3240 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3240 33 34, g32p_row03_traceSegment_069_3240_0033, g32p_row03_traceSegment_069_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3307 8 9, g32p_row03_traceSegment_069_3307_0008, g32p_row03_traceSegment_069_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3332 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3324 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3324 8 9, g32p_row03_traceSegment_069_3324_0008, g32p_row03_traceSegment_069_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3307 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3307 17 17, g32p_row03_traceSegment_069_3307_0017, g32p_row03_traceSegment_069_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3341 8 9, g32p_row03_traceSegment_069_3341_0008, g32p_row03_traceSegment_069_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3358 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3358 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3358 8 9, g32p_row03_traceSegment_069_3358_0008, g32p_row03_traceSegment_069_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3341 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3341 17 17, g32p_row03_traceSegment_069_3341_0017, g32p_row03_traceSegment_069_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 3307 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3307 34 34, g32p_row03_traceSegment_069_3307_0034, g32p_row03_traceSegment_069_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 3240 135 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3240 67 68, g32p_row03_traceSegment_069_3240_0067, g32p_row03_traceSegment_069_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3391 8 9, g32p_row03_traceSegment_069_3391_0008, g32p_row03_traceSegment_069_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3375 16 17, g32p_row03_traceSegment_069_3375_0016, g32p_row03_traceSegment_069_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3408 8 9, g32p_row03_traceSegment_069_3408_0008, g32p_row03_traceSegment_069_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3425 8 9, g32p_row03_traceSegment_069_3425_0008, g32p_row03_traceSegment_069_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3408 17 17, g32p_row03_traceSegment_069_3408_0017, g32p_row03_traceSegment_069_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3375 33 34, g32p_row03_traceSegment_069_3375_0033, g32p_row03_traceSegment_069_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3442 8 9, g32p_row03_traceSegment_069_3442_0008, g32p_row03_traceSegment_069_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3459 8 = [1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3459 17 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3459 8 9, g32p_row03_traceSegment_069_3459_0008, g32p_row03_traceSegment_069_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3442 34 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3442 17 17, g32p_row03_traceSegment_069_3442_0017, g32p_row03_traceSegment_069_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3476 8 9, g32p_row03_traceSegment_069_3476_0008, g32p_row03_traceSegment_069_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3493 8 9, g32p_row03_traceSegment_069_3493_0008, g32p_row03_traceSegment_069_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3476 17 17, g32p_row03_traceSegment_069_3476_0017, g32p_row03_traceSegment_069_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 3442 68 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3442 34 34, g32p_row03_traceSegment_069_3442_0034, g32p_row03_traceSegment_069_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 3375 135 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3375 67 68, g32p_row03_traceSegment_069_3375_0067, g32p_row03_traceSegment_069_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 3240 270 = [1, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3240 135 135, g32p_row03_traceSegment_069_3240_0135, g32p_row03_traceSegment_069_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3526 8 9, g32p_row03_traceSegment_069_3526_0008, g32p_row03_traceSegment_069_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3510 16 17, g32p_row03_traceSegment_069_3510_0016, g32p_row03_traceSegment_069_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3551 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3543 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3543 8 9, g32p_row03_traceSegment_069_3543_0008, g32p_row03_traceSegment_069_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3560 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3560 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3560 8 9, g32p_row03_traceSegment_069_3560_0008, g32p_row03_traceSegment_069_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3543 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3543 17 17, g32p_row03_traceSegment_069_3543_0017, g32p_row03_traceSegment_069_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 3510 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3510 33 34, g32p_row03_traceSegment_069_3510_0033, g32p_row03_traceSegment_069_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3577 8 9, g32p_row03_traceSegment_069_3577_0008, g32p_row03_traceSegment_069_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3594 8 9, g32p_row03_traceSegment_069_3594_0008, g32p_row03_traceSegment_069_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3577 17 17, g32p_row03_traceSegment_069_3577_0017, g32p_row03_traceSegment_069_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3611 8 9, g32p_row03_traceSegment_069_3611_0008, g32p_row03_traceSegment_069_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3628 8 9, g32p_row03_traceSegment_069_3628_0008, g32p_row03_traceSegment_069_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3611 17 17, g32p_row03_traceSegment_069_3611_0017, g32p_row03_traceSegment_069_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3577 34 34, g32p_row03_traceSegment_069_3577_0034, g32p_row03_traceSegment_069_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 3510 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3510 67 68, g32p_row03_traceSegment_069_3510_0067, g32p_row03_traceSegment_069_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3669 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3661 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3661 8 9, g32p_row03_traceSegment_069_3661_0008, g32p_row03_traceSegment_069_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 3645 33 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3645 16 17, g32p_row03_traceSegment_069_3645_0016, g32p_row03_traceSegment_069_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3678 8 9, g32p_row03_traceSegment_069_3678_0008, g32p_row03_traceSegment_069_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3703 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3695 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3695 8 9, g32p_row03_traceSegment_069_3695_0008, g32p_row03_traceSegment_069_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3678 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3678 17 17, g32p_row03_traceSegment_069_3678_0017, g32p_row03_traceSegment_069_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 3645 67 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3645 33 34, g32p_row03_traceSegment_069_3645_0033, g32p_row03_traceSegment_069_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3712 8 9, g32p_row03_traceSegment_069_3712_0008, g32p_row03_traceSegment_069_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3737 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3729 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3729 8 9, g32p_row03_traceSegment_069_3729_0008, g32p_row03_traceSegment_069_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3712 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3712 17 17, g32p_row03_traceSegment_069_3712_0017, g32p_row03_traceSegment_069_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3746 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3754 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3746 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3746 8 9, g32p_row03_traceSegment_069_3746_0008, g32p_row03_traceSegment_069_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3763 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3763 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3763 8 9, g32p_row03_traceSegment_069_3763_0008, g32p_row03_traceSegment_069_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3746 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3746 17 17, g32p_row03_traceSegment_069_3746_0017, g32p_row03_traceSegment_069_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 3712 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3712 34 34, g32p_row03_traceSegment_069_3712_0034, g32p_row03_traceSegment_069_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 3645 135 = [6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3645 67 68, g32p_row03_traceSegment_069_3645_0067, g32p_row03_traceSegment_069_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 3510 270 = [6, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3510 135 135, g32p_row03_traceSegment_069_3510_0135, g32p_row03_traceSegment_069_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_069 3240 540 = [7, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3240 270 270, g32p_row03_traceSegment_069_3240_0270, g32p_row03_traceSegment_069_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 3780 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3796 8 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3796 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3796 8 9, g32p_row03_traceSegment_069_3796_0008, g32p_row03_traceSegment_069_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 3780 33 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3780 16 17, g32p_row03_traceSegment_069_3780_0016, g32p_row03_traceSegment_069_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3813 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3813 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3813 8 9, g32p_row03_traceSegment_069_3813_0008, g32p_row03_traceSegment_069_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3838 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3830 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3830 8 9, g32p_row03_traceSegment_069_3830_0008, g32p_row03_traceSegment_069_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3813 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3813 17 17, g32p_row03_traceSegment_069_3813_0017, g32p_row03_traceSegment_069_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 3780 67 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3780 33 34, g32p_row03_traceSegment_069_3780_0033, g32p_row03_traceSegment_069_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3847 8 9, g32p_row03_traceSegment_069_3847_0008, g32p_row03_traceSegment_069_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3864 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3864 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3864 8 9, g32p_row03_traceSegment_069_3864_0008, g32p_row03_traceSegment_069_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3847 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3847 17 17, g32p_row03_traceSegment_069_3847_0017, g32p_row03_traceSegment_069_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3881 8 9, g32p_row03_traceSegment_069_3881_0008, g32p_row03_traceSegment_069_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3898 8 9, g32p_row03_traceSegment_069_3898_0008, g32p_row03_traceSegment_069_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3881 17 17, g32p_row03_traceSegment_069_3881_0017, g32p_row03_traceSegment_069_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 3847 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3847 34 34, g32p_row03_traceSegment_069_3847_0034, g32p_row03_traceSegment_069_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 3780 135 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3780 67 68, g32p_row03_traceSegment_069_3780_0067, g32p_row03_traceSegment_069_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3931 8 9, g32p_row03_traceSegment_069_3931_0008, g32p_row03_traceSegment_069_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3915 16 17, g32p_row03_traceSegment_069_3915_0016, g32p_row03_traceSegment_069_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3948 8 9, g32p_row03_traceSegment_069_3948_0008, g32p_row03_traceSegment_069_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3965 8 9, g32p_row03_traceSegment_069_3965_0008, g32p_row03_traceSegment_069_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3948 17 17, g32p_row03_traceSegment_069_3948_0017, g32p_row03_traceSegment_069_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3915 33 34, g32p_row03_traceSegment_069_3915_0033, g32p_row03_traceSegment_069_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3982 8 9, g32p_row03_traceSegment_069_3982_0008, g32p_row03_traceSegment_069_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3999 8 9, g32p_row03_traceSegment_069_3999_0008, g32p_row03_traceSegment_069_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3982 17 17, g32p_row03_traceSegment_069_3982_0017, g32p_row03_traceSegment_069_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4016 8 9, g32p_row03_traceSegment_069_4016_0008, g32p_row03_traceSegment_069_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4033 8 9, g32p_row03_traceSegment_069_4033_0008, g32p_row03_traceSegment_069_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4016 17 17, g32p_row03_traceSegment_069_4016_0017, g32p_row03_traceSegment_069_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3982 34 34, g32p_row03_traceSegment_069_3982_0034, g32p_row03_traceSegment_069_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3915 67 68, g32p_row03_traceSegment_069_3915_0067, g32p_row03_traceSegment_069_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 3780 270 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3780 135 135, g32p_row03_traceSegment_069_3780_0135, g32p_row03_traceSegment_069_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4066 8 9, g32p_row03_traceSegment_069_4066_0008, g32p_row03_traceSegment_069_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4050 16 17, g32p_row03_traceSegment_069_4050_0016, g32p_row03_traceSegment_069_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4083 8 9, g32p_row03_traceSegment_069_4083_0008, g32p_row03_traceSegment_069_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4100 8 9, g32p_row03_traceSegment_069_4100_0008, g32p_row03_traceSegment_069_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4083 17 17, g32p_row03_traceSegment_069_4083_0017, g32p_row03_traceSegment_069_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4050 33 34, g32p_row03_traceSegment_069_4050_0033, g32p_row03_traceSegment_069_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4117 8 9, g32p_row03_traceSegment_069_4117_0008, g32p_row03_traceSegment_069_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4134 8 9, g32p_row03_traceSegment_069_4134_0008, g32p_row03_traceSegment_069_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4117 17 17, g32p_row03_traceSegment_069_4117_0017, g32p_row03_traceSegment_069_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4159 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4151 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4151 8 9, g32p_row03_traceSegment_069_4151_0008, g32p_row03_traceSegment_069_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4168 8 9, g32p_row03_traceSegment_069_4168_0008, g32p_row03_traceSegment_069_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 4151 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4151 17 17, g32p_row03_traceSegment_069_4151_0017, g32p_row03_traceSegment_069_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 4117 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4117 34 34, g32p_row03_traceSegment_069_4117_0034, g32p_row03_traceSegment_069_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 4050 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4050 67 68, g32p_row03_traceSegment_069_4050_0067, g32p_row03_traceSegment_069_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_069 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4201 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4201 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4201 8 9, g32p_row03_traceSegment_069_4201_0008, g32p_row03_traceSegment_069_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_069 4185 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4185 16 17, g32p_row03_traceSegment_069_4185_0016, g32p_row03_traceSegment_069_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4226 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4218 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4218 8 9, g32p_row03_traceSegment_069_4218_0008, g32p_row03_traceSegment_069_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4235 8 9, g32p_row03_traceSegment_069_4235_0008, g32p_row03_traceSegment_069_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 4218 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4218 17 17, g32p_row03_traceSegment_069_4218_0017, g32p_row03_traceSegment_069_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_069 4185 67 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4185 33 34, g32p_row03_traceSegment_069_4185_0033, g32p_row03_traceSegment_069_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4260 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4252 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4252 8 9, g32p_row03_traceSegment_069_4252_0008, g32p_row03_traceSegment_069_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4269 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4269 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4269 8 9, g32p_row03_traceSegment_069_4269_0008, g32p_row03_traceSegment_069_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 4252 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4252 17 17, g32p_row03_traceSegment_069_4252_0017, g32p_row03_traceSegment_069_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4294 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4286 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4286 8 9, g32p_row03_traceSegment_069_4286_0008, g32p_row03_traceSegment_069_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_069 4303 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_069 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_069_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_069 4303 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4303 8 9, g32p_row03_traceSegment_069_4303_0008, g32p_row03_traceSegment_069_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_069 4286 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4286 17 17, g32p_row03_traceSegment_069_4286_0017, g32p_row03_traceSegment_069_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_069 4252 68 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4252 34 34, g32p_row03_traceSegment_069_4252_0034, g32p_row03_traceSegment_069_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_069 4185 135 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4185 67 68, g32p_row03_traceSegment_069_4185_0067, g32p_row03_traceSegment_069_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_069_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_069 4050 270 = [1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 4050 135 135, g32p_row03_traceSegment_069_4050_0135, g32p_row03_traceSegment_069_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_069 3780 540 = [9, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3780 270 270, g32p_row03_traceSegment_069_3780_0270, g32p_row03_traceSegment_069_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_069_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_069 3240 1080 = [16, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 3240 540 540, g32p_row03_traceSegment_069_3240_0540, g32p_row03_traceSegment_069_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_069_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_069 2160 2160 = [36, 0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 2160 1080 1080, g32p_row03_traceSegment_069_2160_1080, g32p_row03_traceSegment_069_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_069_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_069 0 4320 = [90, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_069 0 2160 2160, g32p_row03_traceSegment_069_0000_2160, g32p_row03_traceSegment_069_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 69 = [90, 0, 0, 30] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_069_0000_4320

end HodgeLean.Foundations.Program

end
end
