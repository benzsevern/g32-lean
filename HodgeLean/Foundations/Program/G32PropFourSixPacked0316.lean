import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_011 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 11 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_011_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 16 8 9, g32p_row03_traceSegment_011_0016_0008, g32p_row03_traceSegment_011_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 0 16 17, g32p_row03_traceSegment_011_0000_0016, g32p_row03_traceSegment_011_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 33 8 9, g32p_row03_traceSegment_011_0033_0008, g32p_row03_traceSegment_011_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 50 8 9, g32p_row03_traceSegment_011_0050_0008, g32p_row03_traceSegment_011_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 33 17 17, g32p_row03_traceSegment_011_0033_0017, g32p_row03_traceSegment_011_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 0 33 34, g32p_row03_traceSegment_011_0000_0033, g32p_row03_traceSegment_011_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 67 8 9, g32p_row03_traceSegment_011_0067_0008, g32p_row03_traceSegment_011_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 84 8 9, g32p_row03_traceSegment_011_0084_0008, g32p_row03_traceSegment_011_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 67 17 17, g32p_row03_traceSegment_011_0067_0017, g32p_row03_traceSegment_011_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 101 8 9, g32p_row03_traceSegment_011_0101_0008, g32p_row03_traceSegment_011_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 118 8 9, g32p_row03_traceSegment_011_0118_0008, g32p_row03_traceSegment_011_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 101 17 17, g32p_row03_traceSegment_011_0101_0017, g32p_row03_traceSegment_011_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 67 34 34, g32p_row03_traceSegment_011_0067_0034, g32p_row03_traceSegment_011_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 0 67 68, g32p_row03_traceSegment_011_0000_0067, g32p_row03_traceSegment_011_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 151 8 9, g32p_row03_traceSegment_011_0151_0008, g32p_row03_traceSegment_011_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 135 16 17, g32p_row03_traceSegment_011_0135_0016, g32p_row03_traceSegment_011_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 168 8 9, g32p_row03_traceSegment_011_0168_0008, g32p_row03_traceSegment_011_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 185 8 9, g32p_row03_traceSegment_011_0185_0008, g32p_row03_traceSegment_011_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 168 17 17, g32p_row03_traceSegment_011_0168_0017, g32p_row03_traceSegment_011_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 135 33 34, g32p_row03_traceSegment_011_0135_0033, g32p_row03_traceSegment_011_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 202 8 9, g32p_row03_traceSegment_011_0202_0008, g32p_row03_traceSegment_011_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 219 8 9, g32p_row03_traceSegment_011_0219_0008, g32p_row03_traceSegment_011_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 202 17 17, g32p_row03_traceSegment_011_0202_0017, g32p_row03_traceSegment_011_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 236 8 9, g32p_row03_traceSegment_011_0236_0008, g32p_row03_traceSegment_011_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 261 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 253 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 253 8 9, g32p_row03_traceSegment_011_0253_0008, g32p_row03_traceSegment_011_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 236 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 236 17 17, g32p_row03_traceSegment_011_0236_0017, g32p_row03_traceSegment_011_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 202 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 202 34 34, g32p_row03_traceSegment_011_0202_0034, g32p_row03_traceSegment_011_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 135 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 135 67 68, g32p_row03_traceSegment_011_0135_0067, g32p_row03_traceSegment_011_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 0 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 0 135 135, g32p_row03_traceSegment_011_0000_0135, g32p_row03_traceSegment_011_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 294 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 286 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 286 8 9, g32p_row03_traceSegment_011_0286_0008, g32p_row03_traceSegment_011_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 270 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 270 16 17, g32p_row03_traceSegment_011_0270_0016, g32p_row03_traceSegment_011_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 303 8 9, g32p_row03_traceSegment_011_0303_0008, g32p_row03_traceSegment_011_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 328 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 320 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 320 8 9, g32p_row03_traceSegment_011_0320_0008, g32p_row03_traceSegment_011_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 303 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 303 17 17, g32p_row03_traceSegment_011_0303_0017, g32p_row03_traceSegment_011_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 270 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 270 33 34, g32p_row03_traceSegment_011_0270_0033, g32p_row03_traceSegment_011_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 337 8 9, g32p_row03_traceSegment_011_0337_0008, g32p_row03_traceSegment_011_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 362 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 354 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 354 8 9, g32p_row03_traceSegment_011_0354_0008, g32p_row03_traceSegment_011_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 337 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 337 17 17, g32p_row03_traceSegment_011_0337_0017, g32p_row03_traceSegment_011_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 371 8 9, g32p_row03_traceSegment_011_0371_0008, g32p_row03_traceSegment_011_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 388 8 9, g32p_row03_traceSegment_011_0388_0008, g32p_row03_traceSegment_011_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 371 17 17, g32p_row03_traceSegment_011_0371_0017, g32p_row03_traceSegment_011_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 337 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 337 34 34, g32p_row03_traceSegment_011_0337_0034, g32p_row03_traceSegment_011_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 270 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 270 67 68, g32p_row03_traceSegment_011_0270_0067, g32p_row03_traceSegment_011_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 421 8 9, g32p_row03_traceSegment_011_0421_0008, g32p_row03_traceSegment_011_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 405 16 17, g32p_row03_traceSegment_011_0405_0016, g32p_row03_traceSegment_011_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 438 8 9, g32p_row03_traceSegment_011_0438_0008, g32p_row03_traceSegment_011_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 455 8 9, g32p_row03_traceSegment_011_0455_0008, g32p_row03_traceSegment_011_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 438 17 17, g32p_row03_traceSegment_011_0438_0017, g32p_row03_traceSegment_011_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 405 33 34, g32p_row03_traceSegment_011_0405_0033, g32p_row03_traceSegment_011_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 472 8 9, g32p_row03_traceSegment_011_0472_0008, g32p_row03_traceSegment_011_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 489 8 9, g32p_row03_traceSegment_011_0489_0008, g32p_row03_traceSegment_011_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 472 17 17, g32p_row03_traceSegment_011_0472_0017, g32p_row03_traceSegment_011_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 506 8 9, g32p_row03_traceSegment_011_0506_0008, g32p_row03_traceSegment_011_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 523 8 9, g32p_row03_traceSegment_011_0523_0008, g32p_row03_traceSegment_011_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 506 17 17, g32p_row03_traceSegment_011_0506_0017, g32p_row03_traceSegment_011_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 472 34 34, g32p_row03_traceSegment_011_0472_0034, g32p_row03_traceSegment_011_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 405 67 68, g32p_row03_traceSegment_011_0405_0067, g32p_row03_traceSegment_011_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 270 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 270 135 135, g32p_row03_traceSegment_011_0270_0135, g32p_row03_traceSegment_011_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_011 0 540 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 0 270 270, g32p_row03_traceSegment_011_0000_0270, g32p_row03_traceSegment_011_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 556 8 9, g32p_row03_traceSegment_011_0556_0008, g32p_row03_traceSegment_011_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 540 16 17, g32p_row03_traceSegment_011_0540_0016, g32p_row03_traceSegment_011_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 573 8 9, g32p_row03_traceSegment_011_0573_0008, g32p_row03_traceSegment_011_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 590 8 9, g32p_row03_traceSegment_011_0590_0008, g32p_row03_traceSegment_011_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 573 17 17, g32p_row03_traceSegment_011_0573_0017, g32p_row03_traceSegment_011_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 540 33 34, g32p_row03_traceSegment_011_0540_0033, g32p_row03_traceSegment_011_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 607 8 9, g32p_row03_traceSegment_011_0607_0008, g32p_row03_traceSegment_011_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 624 8 9, g32p_row03_traceSegment_011_0624_0008, g32p_row03_traceSegment_011_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 607 17 17, g32p_row03_traceSegment_011_0607_0017, g32p_row03_traceSegment_011_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 641 8 9, g32p_row03_traceSegment_011_0641_0008, g32p_row03_traceSegment_011_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 658 8 9, g32p_row03_traceSegment_011_0658_0008, g32p_row03_traceSegment_011_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 641 17 17, g32p_row03_traceSegment_011_0641_0017, g32p_row03_traceSegment_011_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 607 34 34, g32p_row03_traceSegment_011_0607_0034, g32p_row03_traceSegment_011_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 540 67 68, g32p_row03_traceSegment_011_0540_0067, g32p_row03_traceSegment_011_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 691 8 9, g32p_row03_traceSegment_011_0691_0008, g32p_row03_traceSegment_011_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 675 16 17, g32p_row03_traceSegment_011_0675_0016, g32p_row03_traceSegment_011_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 708 8 9, g32p_row03_traceSegment_011_0708_0008, g32p_row03_traceSegment_011_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 733 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 725 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 725 8 9, g32p_row03_traceSegment_011_0725_0008, g32p_row03_traceSegment_011_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 708 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 708 17 17, g32p_row03_traceSegment_011_0708_0017, g32p_row03_traceSegment_011_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 675 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 675 33 34, g32p_row03_traceSegment_011_0675_0033, g32p_row03_traceSegment_011_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 750 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 742 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 742 8 9, g32p_row03_traceSegment_011_0742_0008, g32p_row03_traceSegment_011_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 759 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 759 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 759 8 9, g32p_row03_traceSegment_011_0759_0008, g32p_row03_traceSegment_011_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 742 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 742 17 17, g32p_row03_traceSegment_011_0742_0017, g32p_row03_traceSegment_011_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 776 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 776 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 776 8 9, g32p_row03_traceSegment_011_0776_0008, g32p_row03_traceSegment_011_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 793 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 793 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 793 8 9, g32p_row03_traceSegment_011_0793_0008, g32p_row03_traceSegment_011_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 776 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 776 17 17, g32p_row03_traceSegment_011_0776_0017, g32p_row03_traceSegment_011_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 742 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 742 34 34, g32p_row03_traceSegment_011_0742_0034, g32p_row03_traceSegment_011_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 675 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 675 67 68, g32p_row03_traceSegment_011_0675_0067, g32p_row03_traceSegment_011_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 540 270 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 540 135 135, g32p_row03_traceSegment_011_0540_0135, g32p_row03_traceSegment_011_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 834 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 826 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 826 8 9, g32p_row03_traceSegment_011_0826_0008, g32p_row03_traceSegment_011_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 810 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 810 16 17, g32p_row03_traceSegment_011_0810_0016, g32p_row03_traceSegment_011_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 843 8 9, g32p_row03_traceSegment_011_0843_0008, g32p_row03_traceSegment_011_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 860 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 860 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 860 8 9, g32p_row03_traceSegment_011_0860_0008, g32p_row03_traceSegment_011_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 843 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 843 17 17, g32p_row03_traceSegment_011_0843_0017, g32p_row03_traceSegment_011_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 810 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 810 33 34, g32p_row03_traceSegment_011_0810_0033, g32p_row03_traceSegment_011_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 877 8 9, g32p_row03_traceSegment_011_0877_0008, g32p_row03_traceSegment_011_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 894 8 9, g32p_row03_traceSegment_011_0894_0008, g32p_row03_traceSegment_011_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 877 17 17, g32p_row03_traceSegment_011_0877_0017, g32p_row03_traceSegment_011_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 911 8 9, g32p_row03_traceSegment_011_0911_0008, g32p_row03_traceSegment_011_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 936 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 928 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 928 8 9, g32p_row03_traceSegment_011_0928_0008, g32p_row03_traceSegment_011_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 911 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 911 17 17, g32p_row03_traceSegment_011_0911_0017, g32p_row03_traceSegment_011_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 877 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 877 34 34, g32p_row03_traceSegment_011_0877_0034, g32p_row03_traceSegment_011_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 810 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 810 67 68, g32p_row03_traceSegment_011_0810_0067, g32p_row03_traceSegment_011_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 961 8 9, g32p_row03_traceSegment_011_0961_0008, g32p_row03_traceSegment_011_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 945 16 17, g32p_row03_traceSegment_011_0945_0016, g32p_row03_traceSegment_011_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 978 8 9, g32p_row03_traceSegment_011_0978_0008, g32p_row03_traceSegment_011_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 995 8 9, g32p_row03_traceSegment_011_0995_0008, g32p_row03_traceSegment_011_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 978 17 17, g32p_row03_traceSegment_011_0978_0017, g32p_row03_traceSegment_011_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 945 33 34, g32p_row03_traceSegment_011_0945_0033, g32p_row03_traceSegment_011_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1012 8 9, g32p_row03_traceSegment_011_1012_0008, g32p_row03_traceSegment_011_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1029 8 9, g32p_row03_traceSegment_011_1029_0008, g32p_row03_traceSegment_011_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1012 17 17, g32p_row03_traceSegment_011_1012_0017, g32p_row03_traceSegment_011_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1046 8 9, g32p_row03_traceSegment_011_1046_0008, g32p_row03_traceSegment_011_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1063 8 9, g32p_row03_traceSegment_011_1063_0008, g32p_row03_traceSegment_011_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1046 17 17, g32p_row03_traceSegment_011_1046_0017, g32p_row03_traceSegment_011_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1012 34 34, g32p_row03_traceSegment_011_1012_0034, g32p_row03_traceSegment_011_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 945 67 68, g32p_row03_traceSegment_011_0945_0067, g32p_row03_traceSegment_011_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 810 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 810 135 135, g32p_row03_traceSegment_011_0810_0135, g32p_row03_traceSegment_011_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_011 540 540 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 540 270 270, g32p_row03_traceSegment_011_0540_0270, g32p_row03_traceSegment_011_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_011 0 1080 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 0 540 540, g32p_row03_traceSegment_011_0000_0540, g32p_row03_traceSegment_011_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1096 8 9, g32p_row03_traceSegment_011_1096_0008, g32p_row03_traceSegment_011_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1080 16 17, g32p_row03_traceSegment_011_1080_0016, g32p_row03_traceSegment_011_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1113 8 9, g32p_row03_traceSegment_011_1113_0008, g32p_row03_traceSegment_011_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1130 8 9, g32p_row03_traceSegment_011_1130_0008, g32p_row03_traceSegment_011_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1113 17 17, g32p_row03_traceSegment_011_1113_0017, g32p_row03_traceSegment_011_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1080 33 34, g32p_row03_traceSegment_011_1080_0033, g32p_row03_traceSegment_011_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1147 8 9, g32p_row03_traceSegment_011_1147_0008, g32p_row03_traceSegment_011_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1164 8 9, g32p_row03_traceSegment_011_1164_0008, g32p_row03_traceSegment_011_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1147 17 17, g32p_row03_traceSegment_011_1147_0017, g32p_row03_traceSegment_011_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1181 8 9, g32p_row03_traceSegment_011_1181_0008, g32p_row03_traceSegment_011_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1198 8 9, g32p_row03_traceSegment_011_1198_0008, g32p_row03_traceSegment_011_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1181 17 17, g32p_row03_traceSegment_011_1181_0017, g32p_row03_traceSegment_011_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1147 34 34, g32p_row03_traceSegment_011_1147_0034, g32p_row03_traceSegment_011_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1080 67 68, g32p_row03_traceSegment_011_1080_0067, g32p_row03_traceSegment_011_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1231 8 9, g32p_row03_traceSegment_011_1231_0008, g32p_row03_traceSegment_011_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1215 16 17, g32p_row03_traceSegment_011_1215_0016, g32p_row03_traceSegment_011_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1248 8 9, g32p_row03_traceSegment_011_1248_0008, g32p_row03_traceSegment_011_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1265 8 9, g32p_row03_traceSegment_011_1265_0008, g32p_row03_traceSegment_011_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1248 17 17, g32p_row03_traceSegment_011_1248_0017, g32p_row03_traceSegment_011_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1215 33 34, g32p_row03_traceSegment_011_1215_0033, g32p_row03_traceSegment_011_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1282 8 9, g32p_row03_traceSegment_011_1282_0008, g32p_row03_traceSegment_011_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1299 8 9, g32p_row03_traceSegment_011_1299_0008, g32p_row03_traceSegment_011_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1282 17 17, g32p_row03_traceSegment_011_1282_0017, g32p_row03_traceSegment_011_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1316 8 9, g32p_row03_traceSegment_011_1316_0008, g32p_row03_traceSegment_011_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1333 8 9, g32p_row03_traceSegment_011_1333_0008, g32p_row03_traceSegment_011_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1316 17 17, g32p_row03_traceSegment_011_1316_0017, g32p_row03_traceSegment_011_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1282 34 34, g32p_row03_traceSegment_011_1282_0034, g32p_row03_traceSegment_011_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1215 67 68, g32p_row03_traceSegment_011_1215_0067, g32p_row03_traceSegment_011_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1080 135 135, g32p_row03_traceSegment_011_1080_0135, g32p_row03_traceSegment_011_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1366 8 9, g32p_row03_traceSegment_011_1366_0008, g32p_row03_traceSegment_011_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1350 16 17, g32p_row03_traceSegment_011_1350_0016, g32p_row03_traceSegment_011_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1383 8 9, g32p_row03_traceSegment_011_1383_0008, g32p_row03_traceSegment_011_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1400 8 9, g32p_row03_traceSegment_011_1400_0008, g32p_row03_traceSegment_011_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1383 17 17, g32p_row03_traceSegment_011_1383_0017, g32p_row03_traceSegment_011_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1350 33 34, g32p_row03_traceSegment_011_1350_0033, g32p_row03_traceSegment_011_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1417 8 9, g32p_row03_traceSegment_011_1417_0008, g32p_row03_traceSegment_011_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1434 8 9, g32p_row03_traceSegment_011_1434_0008, g32p_row03_traceSegment_011_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1417 17 17, g32p_row03_traceSegment_011_1417_0017, g32p_row03_traceSegment_011_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1451 8 9, g32p_row03_traceSegment_011_1451_0008, g32p_row03_traceSegment_011_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1468 8 9, g32p_row03_traceSegment_011_1468_0008, g32p_row03_traceSegment_011_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1451 17 17, g32p_row03_traceSegment_011_1451_0017, g32p_row03_traceSegment_011_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1417 34 34, g32p_row03_traceSegment_011_1417_0034, g32p_row03_traceSegment_011_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1350 67 68, g32p_row03_traceSegment_011_1350_0067, g32p_row03_traceSegment_011_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 1485 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1501 8 9, g32p_row03_traceSegment_011_1501_0008, g32p_row03_traceSegment_011_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 1485 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1485 16 17, g32p_row03_traceSegment_011_1485_0016, g32p_row03_traceSegment_011_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1518 8 9, g32p_row03_traceSegment_011_1518_0008, g32p_row03_traceSegment_011_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1543 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1535 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1535 8 9, g32p_row03_traceSegment_011_1535_0008, g32p_row03_traceSegment_011_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1518 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1518 17 17, g32p_row03_traceSegment_011_1518_0017, g32p_row03_traceSegment_011_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 1485 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1485 33 34, g32p_row03_traceSegment_011_1485_0033, g32p_row03_traceSegment_011_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1552 8 9, g32p_row03_traceSegment_011_1552_0008, g32p_row03_traceSegment_011_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1569 8 9, g32p_row03_traceSegment_011_1569_0008, g32p_row03_traceSegment_011_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1552 17 17, g32p_row03_traceSegment_011_1552_0017, g32p_row03_traceSegment_011_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1586 8 9, g32p_row03_traceSegment_011_1586_0008, g32p_row03_traceSegment_011_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1603 8 9, g32p_row03_traceSegment_011_1603_0008, g32p_row03_traceSegment_011_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1586 17 17, g32p_row03_traceSegment_011_1586_0017, g32p_row03_traceSegment_011_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1552 34 34, g32p_row03_traceSegment_011_1552_0034, g32p_row03_traceSegment_011_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 1485 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1485 67 68, g32p_row03_traceSegment_011_1485_0067, g32p_row03_traceSegment_011_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 1350 270 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1350 135 135, g32p_row03_traceSegment_011_1350_0135, g32p_row03_traceSegment_011_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_011 1080 540 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1080 270 270, g32p_row03_traceSegment_011_1080_0270, g32p_row03_traceSegment_011_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1636 8 9, g32p_row03_traceSegment_011_1636_0008, g32p_row03_traceSegment_011_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1620 16 17, g32p_row03_traceSegment_011_1620_0016, g32p_row03_traceSegment_011_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1653 8 9, g32p_row03_traceSegment_011_1653_0008, g32p_row03_traceSegment_011_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1670 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1678 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1670 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1670 8 9, g32p_row03_traceSegment_011_1670_0008, g32p_row03_traceSegment_011_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1653 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1653 17 17, g32p_row03_traceSegment_011_1653_0017, g32p_row03_traceSegment_011_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 1620 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1620 33 34, g32p_row03_traceSegment_011_1620_0033, g32p_row03_traceSegment_011_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1687 8 9, g32p_row03_traceSegment_011_1687_0008, g32p_row03_traceSegment_011_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1704 8 9, g32p_row03_traceSegment_011_1704_0008, g32p_row03_traceSegment_011_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1687 17 17, g32p_row03_traceSegment_011_1687_0017, g32p_row03_traceSegment_011_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1721 8 9, g32p_row03_traceSegment_011_1721_0008, g32p_row03_traceSegment_011_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1738 8 9, g32p_row03_traceSegment_011_1738_0008, g32p_row03_traceSegment_011_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1721 17 17, g32p_row03_traceSegment_011_1721_0017, g32p_row03_traceSegment_011_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1687 34 34, g32p_row03_traceSegment_011_1687_0034, g32p_row03_traceSegment_011_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 1620 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1620 67 68, g32p_row03_traceSegment_011_1620_0067, g32p_row03_traceSegment_011_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 1755 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1771 8 9, g32p_row03_traceSegment_011_1771_0008, g32p_row03_traceSegment_011_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 1755 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1755 16 17, g32p_row03_traceSegment_011_1755_0016, g32p_row03_traceSegment_011_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1788 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1788 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1788 8 9, g32p_row03_traceSegment_011_1788_0008, g32p_row03_traceSegment_011_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1805 8 9, g32p_row03_traceSegment_011_1805_0008, g32p_row03_traceSegment_011_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1788 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1788 17 17, g32p_row03_traceSegment_011_1788_0017, g32p_row03_traceSegment_011_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 1755 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1755 33 34, g32p_row03_traceSegment_011_1755_0033, g32p_row03_traceSegment_011_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1822 8 9, g32p_row03_traceSegment_011_1822_0008, g32p_row03_traceSegment_011_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1839 8 9, g32p_row03_traceSegment_011_1839_0008, g32p_row03_traceSegment_011_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1822 17 17, g32p_row03_traceSegment_011_1822_0017, g32p_row03_traceSegment_011_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1856 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1856 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1856 8 9, g32p_row03_traceSegment_011_1856_0008, g32p_row03_traceSegment_011_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1873 8 9, g32p_row03_traceSegment_011_1873_0008, g32p_row03_traceSegment_011_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1856 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1856 17 17, g32p_row03_traceSegment_011_1856_0017, g32p_row03_traceSegment_011_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 1822 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1822 34 34, g32p_row03_traceSegment_011_1822_0034, g32p_row03_traceSegment_011_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 1755 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1755 67 68, g32p_row03_traceSegment_011_1755_0067, g32p_row03_traceSegment_011_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 1620 270 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1620 135 135, g32p_row03_traceSegment_011_1620_0135, g32p_row03_traceSegment_011_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1906 8 9, g32p_row03_traceSegment_011_1906_0008, g32p_row03_traceSegment_011_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1890 16 17, g32p_row03_traceSegment_011_1890_0016, g32p_row03_traceSegment_011_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1923 8 9, g32p_row03_traceSegment_011_1923_0008, g32p_row03_traceSegment_011_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1948 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1940 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1940 8 9, g32p_row03_traceSegment_011_1940_0008, g32p_row03_traceSegment_011_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1923 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1923 17 17, g32p_row03_traceSegment_011_1923_0017, g32p_row03_traceSegment_011_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 1890 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1890 33 34, g32p_row03_traceSegment_011_1890_0033, g32p_row03_traceSegment_011_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1957 8 9, g32p_row03_traceSegment_011_1957_0008, g32p_row03_traceSegment_011_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1974 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1974 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1974 8 9, g32p_row03_traceSegment_011_1974_0008, g32p_row03_traceSegment_011_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1957 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1957 17 17, g32p_row03_traceSegment_011_1957_0017, g32p_row03_traceSegment_011_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 1999 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 1991 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1991 8 9, g32p_row03_traceSegment_011_1991_0008, g32p_row03_traceSegment_011_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2008 8 9, g32p_row03_traceSegment_011_2008_0008, g32p_row03_traceSegment_011_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 1991 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1991 17 17, g32p_row03_traceSegment_011_1991_0017, g32p_row03_traceSegment_011_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 1957 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1957 34 34, g32p_row03_traceSegment_011_1957_0034, g32p_row03_traceSegment_011_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 1890 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1890 67 68, g32p_row03_traceSegment_011_1890_0067, g32p_row03_traceSegment_011_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 2025 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2041 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2041 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2041 8 9, g32p_row03_traceSegment_011_2041_0008, g32p_row03_traceSegment_011_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 2025 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2025 16 17, g32p_row03_traceSegment_011_2025_0016, g32p_row03_traceSegment_011_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2066 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2058 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2058 8 9, g32p_row03_traceSegment_011_2058_0008, g32p_row03_traceSegment_011_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2075 8 9, g32p_row03_traceSegment_011_2075_0008, g32p_row03_traceSegment_011_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2058 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2058 17 17, g32p_row03_traceSegment_011_2058_0017, g32p_row03_traceSegment_011_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 2025 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2025 33 34, g32p_row03_traceSegment_011_2025_0033, g32p_row03_traceSegment_011_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2100 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2092 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2092 8 9, g32p_row03_traceSegment_011_2092_0008, g32p_row03_traceSegment_011_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2109 8 9, g32p_row03_traceSegment_011_2109_0008, g32p_row03_traceSegment_011_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2092 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2092 17 17, g32p_row03_traceSegment_011_2092_0017, g32p_row03_traceSegment_011_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2126 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2126 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2126 8 9, g32p_row03_traceSegment_011_2126_0008, g32p_row03_traceSegment_011_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2143 8 9, g32p_row03_traceSegment_011_2143_0008, g32p_row03_traceSegment_011_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2126 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2126 17 17, g32p_row03_traceSegment_011_2126_0017, g32p_row03_traceSegment_011_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 2092 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2092 34 34, g32p_row03_traceSegment_011_2092_0034, g32p_row03_traceSegment_011_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 2025 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2025 67 68, g32p_row03_traceSegment_011_2025_0067, g32p_row03_traceSegment_011_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 1890 270 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1890 135 135, g32p_row03_traceSegment_011_1890_0135, g32p_row03_traceSegment_011_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_011 1620 540 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1620 270 270, g32p_row03_traceSegment_011_1620_0270, g32p_row03_traceSegment_011_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_011_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_011 1080 1080 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 1080 540 540, g32p_row03_traceSegment_011_1080_0540, g32p_row03_traceSegment_011_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_011 0 2160 = [0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 0 1080 1080, g32p_row03_traceSegment_011_0000_1080, g32p_row03_traceSegment_011_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2176 8 9, g32p_row03_traceSegment_011_2176_0008, g32p_row03_traceSegment_011_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2160 16 17, g32p_row03_traceSegment_011_2160_0016, g32p_row03_traceSegment_011_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2193 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2193 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2193 8 9, g32p_row03_traceSegment_011_2193_0008, g32p_row03_traceSegment_011_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2210 8 9, g32p_row03_traceSegment_011_2210_0008, g32p_row03_traceSegment_011_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2193 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2193 17 17, g32p_row03_traceSegment_011_2193_0017, g32p_row03_traceSegment_011_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 2160 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2160 33 34, g32p_row03_traceSegment_011_2160_0033, g32p_row03_traceSegment_011_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2227 8 9, g32p_row03_traceSegment_011_2227_0008, g32p_row03_traceSegment_011_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2244 8 9, g32p_row03_traceSegment_011_2244_0008, g32p_row03_traceSegment_011_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2227 17 17, g32p_row03_traceSegment_011_2227_0017, g32p_row03_traceSegment_011_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2261 8 9, g32p_row03_traceSegment_011_2261_0008, g32p_row03_traceSegment_011_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2278 8 9, g32p_row03_traceSegment_011_2278_0008, g32p_row03_traceSegment_011_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2261 17 17, g32p_row03_traceSegment_011_2261_0017, g32p_row03_traceSegment_011_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2227 34 34, g32p_row03_traceSegment_011_2227_0034, g32p_row03_traceSegment_011_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 2160 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2160 67 68, g32p_row03_traceSegment_011_2160_0067, g32p_row03_traceSegment_011_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2311 8 9, g32p_row03_traceSegment_011_2311_0008, g32p_row03_traceSegment_011_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2295 16 17, g32p_row03_traceSegment_011_2295_0016, g32p_row03_traceSegment_011_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2328 8 9, g32p_row03_traceSegment_011_2328_0008, g32p_row03_traceSegment_011_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2345 8 9, g32p_row03_traceSegment_011_2345_0008, g32p_row03_traceSegment_011_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2328 17 17, g32p_row03_traceSegment_011_2328_0017, g32p_row03_traceSegment_011_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2295 33 34, g32p_row03_traceSegment_011_2295_0033, g32p_row03_traceSegment_011_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2362 8 9, g32p_row03_traceSegment_011_2362_0008, g32p_row03_traceSegment_011_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2379 8 9, g32p_row03_traceSegment_011_2379_0008, g32p_row03_traceSegment_011_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2362 17 17, g32p_row03_traceSegment_011_2362_0017, g32p_row03_traceSegment_011_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2396 8 9, g32p_row03_traceSegment_011_2396_0008, g32p_row03_traceSegment_011_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2413 8 9, g32p_row03_traceSegment_011_2413_0008, g32p_row03_traceSegment_011_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2396 17 17, g32p_row03_traceSegment_011_2396_0017, g32p_row03_traceSegment_011_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2362 34 34, g32p_row03_traceSegment_011_2362_0034, g32p_row03_traceSegment_011_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2295 67 68, g32p_row03_traceSegment_011_2295_0067, g32p_row03_traceSegment_011_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 2160 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2160 135 135, g32p_row03_traceSegment_011_2160_0135, g32p_row03_traceSegment_011_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2446 8 9, g32p_row03_traceSegment_011_2446_0008, g32p_row03_traceSegment_011_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2430 16 17, g32p_row03_traceSegment_011_2430_0016, g32p_row03_traceSegment_011_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2463 8 9, g32p_row03_traceSegment_011_2463_0008, g32p_row03_traceSegment_011_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2480 8 9, g32p_row03_traceSegment_011_2480_0008, g32p_row03_traceSegment_011_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2463 17 17, g32p_row03_traceSegment_011_2463_0017, g32p_row03_traceSegment_011_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2430 33 34, g32p_row03_traceSegment_011_2430_0033, g32p_row03_traceSegment_011_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2497 8 9, g32p_row03_traceSegment_011_2497_0008, g32p_row03_traceSegment_011_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2514 8 9, g32p_row03_traceSegment_011_2514_0008, g32p_row03_traceSegment_011_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2497 17 17, g32p_row03_traceSegment_011_2497_0017, g32p_row03_traceSegment_011_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2531 8 9, g32p_row03_traceSegment_011_2531_0008, g32p_row03_traceSegment_011_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2548 8 9, g32p_row03_traceSegment_011_2548_0008, g32p_row03_traceSegment_011_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2531 17 17, g32p_row03_traceSegment_011_2531_0017, g32p_row03_traceSegment_011_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2497 34 34, g32p_row03_traceSegment_011_2497_0034, g32p_row03_traceSegment_011_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2430 67 68, g32p_row03_traceSegment_011_2430_0067, g32p_row03_traceSegment_011_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2581 8 9, g32p_row03_traceSegment_011_2581_0008, g32p_row03_traceSegment_011_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2565 16 17, g32p_row03_traceSegment_011_2565_0016, g32p_row03_traceSegment_011_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2598 8 9, g32p_row03_traceSegment_011_2598_0008, g32p_row03_traceSegment_011_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2615 8 9, g32p_row03_traceSegment_011_2615_0008, g32p_row03_traceSegment_011_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2598 17 17, g32p_row03_traceSegment_011_2598_0017, g32p_row03_traceSegment_011_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2565 33 34, g32p_row03_traceSegment_011_2565_0033, g32p_row03_traceSegment_011_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2632 8 9, g32p_row03_traceSegment_011_2632_0008, g32p_row03_traceSegment_011_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2649 8 9, g32p_row03_traceSegment_011_2649_0008, g32p_row03_traceSegment_011_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2632 17 17, g32p_row03_traceSegment_011_2632_0017, g32p_row03_traceSegment_011_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2666 8 9, g32p_row03_traceSegment_011_2666_0008, g32p_row03_traceSegment_011_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2683 8 9, g32p_row03_traceSegment_011_2683_0008, g32p_row03_traceSegment_011_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2666 17 17, g32p_row03_traceSegment_011_2666_0017, g32p_row03_traceSegment_011_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2632 34 34, g32p_row03_traceSegment_011_2632_0034, g32p_row03_traceSegment_011_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2565 67 68, g32p_row03_traceSegment_011_2565_0067, g32p_row03_traceSegment_011_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2430 135 135, g32p_row03_traceSegment_011_2430_0135, g32p_row03_traceSegment_011_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_011 2160 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2160 270 270, g32p_row03_traceSegment_011_2160_0270, g32p_row03_traceSegment_011_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2716 8 9, g32p_row03_traceSegment_011_2716_0008, g32p_row03_traceSegment_011_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2700 16 17, g32p_row03_traceSegment_011_2700_0016, g32p_row03_traceSegment_011_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2733 8 9, g32p_row03_traceSegment_011_2733_0008, g32p_row03_traceSegment_011_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2750 8 9, g32p_row03_traceSegment_011_2750_0008, g32p_row03_traceSegment_011_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2733 17 17, g32p_row03_traceSegment_011_2733_0017, g32p_row03_traceSegment_011_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2700 33 34, g32p_row03_traceSegment_011_2700_0033, g32p_row03_traceSegment_011_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2767 8 9, g32p_row03_traceSegment_011_2767_0008, g32p_row03_traceSegment_011_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2784 8 9, g32p_row03_traceSegment_011_2784_0008, g32p_row03_traceSegment_011_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2767 17 17, g32p_row03_traceSegment_011_2767_0017, g32p_row03_traceSegment_011_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2801 8 9, g32p_row03_traceSegment_011_2801_0008, g32p_row03_traceSegment_011_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2818 8 9, g32p_row03_traceSegment_011_2818_0008, g32p_row03_traceSegment_011_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2801 17 17, g32p_row03_traceSegment_011_2801_0017, g32p_row03_traceSegment_011_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2767 34 34, g32p_row03_traceSegment_011_2767_0034, g32p_row03_traceSegment_011_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2700 67 68, g32p_row03_traceSegment_011_2700_0067, g32p_row03_traceSegment_011_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2851 8 9, g32p_row03_traceSegment_011_2851_0008, g32p_row03_traceSegment_011_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2835 16 17, g32p_row03_traceSegment_011_2835_0016, g32p_row03_traceSegment_011_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2868 8 9, g32p_row03_traceSegment_011_2868_0008, g32p_row03_traceSegment_011_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2885 8 9, g32p_row03_traceSegment_011_2885_0008, g32p_row03_traceSegment_011_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2868 17 17, g32p_row03_traceSegment_011_2868_0017, g32p_row03_traceSegment_011_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2835 33 34, g32p_row03_traceSegment_011_2835_0033, g32p_row03_traceSegment_011_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2902 8 9, g32p_row03_traceSegment_011_2902_0008, g32p_row03_traceSegment_011_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2919 8 9, g32p_row03_traceSegment_011_2919_0008, g32p_row03_traceSegment_011_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2902 17 17, g32p_row03_traceSegment_011_2902_0017, g32p_row03_traceSegment_011_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2936 8 9, g32p_row03_traceSegment_011_2936_0008, g32p_row03_traceSegment_011_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2953 8 9, g32p_row03_traceSegment_011_2953_0008, g32p_row03_traceSegment_011_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2936 17 17, g32p_row03_traceSegment_011_2936_0017, g32p_row03_traceSegment_011_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2902 34 34, g32p_row03_traceSegment_011_2902_0034, g32p_row03_traceSegment_011_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2835 67 68, g32p_row03_traceSegment_011_2835_0067, g32p_row03_traceSegment_011_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2700 135 135, g32p_row03_traceSegment_011_2700_0135, g32p_row03_traceSegment_011_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2986 8 9, g32p_row03_traceSegment_011_2986_0008, g32p_row03_traceSegment_011_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2970 16 17, g32p_row03_traceSegment_011_2970_0016, g32p_row03_traceSegment_011_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3003 8 9, g32p_row03_traceSegment_011_3003_0008, g32p_row03_traceSegment_011_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3020 8 9, g32p_row03_traceSegment_011_3020_0008, g32p_row03_traceSegment_011_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3003 17 17, g32p_row03_traceSegment_011_3003_0017, g32p_row03_traceSegment_011_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2970 33 34, g32p_row03_traceSegment_011_2970_0033, g32p_row03_traceSegment_011_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3037 8 9, g32p_row03_traceSegment_011_3037_0008, g32p_row03_traceSegment_011_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3054 8 9, g32p_row03_traceSegment_011_3054_0008, g32p_row03_traceSegment_011_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3037 17 17, g32p_row03_traceSegment_011_3037_0017, g32p_row03_traceSegment_011_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3071 8 9, g32p_row03_traceSegment_011_3071_0008, g32p_row03_traceSegment_011_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3088 8 9, g32p_row03_traceSegment_011_3088_0008, g32p_row03_traceSegment_011_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3071 17 17, g32p_row03_traceSegment_011_3071_0017, g32p_row03_traceSegment_011_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3037 34 34, g32p_row03_traceSegment_011_3037_0034, g32p_row03_traceSegment_011_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2970 67 68, g32p_row03_traceSegment_011_2970_0067, g32p_row03_traceSegment_011_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3121 8 9, g32p_row03_traceSegment_011_3121_0008, g32p_row03_traceSegment_011_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3105 16 17, g32p_row03_traceSegment_011_3105_0016, g32p_row03_traceSegment_011_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3138 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3138 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3138 8 9, g32p_row03_traceSegment_011_3138_0008, g32p_row03_traceSegment_011_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3155 8 9, g32p_row03_traceSegment_011_3155_0008, g32p_row03_traceSegment_011_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3138 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3138 17 17, g32p_row03_traceSegment_011_3138_0017, g32p_row03_traceSegment_011_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 3105 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3105 33 34, g32p_row03_traceSegment_011_3105_0033, g32p_row03_traceSegment_011_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3172 8 9, g32p_row03_traceSegment_011_3172_0008, g32p_row03_traceSegment_011_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3189 8 9, g32p_row03_traceSegment_011_3189_0008, g32p_row03_traceSegment_011_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3172 17 17, g32p_row03_traceSegment_011_3172_0017, g32p_row03_traceSegment_011_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3206 8 9, g32p_row03_traceSegment_011_3206_0008, g32p_row03_traceSegment_011_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3231 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3223 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3223 8 9, g32p_row03_traceSegment_011_3223_0008, g32p_row03_traceSegment_011_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3206 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3206 17 17, g32p_row03_traceSegment_011_3206_0017, g32p_row03_traceSegment_011_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 3172 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3172 34 34, g32p_row03_traceSegment_011_3172_0034, g32p_row03_traceSegment_011_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 3105 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3105 67 68, g32p_row03_traceSegment_011_3105_0067, g32p_row03_traceSegment_011_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 2970 270 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2970 135 135, g32p_row03_traceSegment_011_2970_0135, g32p_row03_traceSegment_011_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_011 2700 540 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2700 270 270, g32p_row03_traceSegment_011_2700_0270, g32p_row03_traceSegment_011_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_011 2160 1080 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2160 540 540, g32p_row03_traceSegment_011_2160_0540, g32p_row03_traceSegment_011_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3256 8 9, g32p_row03_traceSegment_011_3256_0008, g32p_row03_traceSegment_011_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3240 16 17, g32p_row03_traceSegment_011_3240_0016, g32p_row03_traceSegment_011_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3273 8 9, g32p_row03_traceSegment_011_3273_0008, g32p_row03_traceSegment_011_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3290 8 9, g32p_row03_traceSegment_011_3290_0008, g32p_row03_traceSegment_011_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3273 17 17, g32p_row03_traceSegment_011_3273_0017, g32p_row03_traceSegment_011_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3240 33 34, g32p_row03_traceSegment_011_3240_0033, g32p_row03_traceSegment_011_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3315 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3307 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3307 8 9, g32p_row03_traceSegment_011_3307_0008, g32p_row03_traceSegment_011_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3324 8 9, g32p_row03_traceSegment_011_3324_0008, g32p_row03_traceSegment_011_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3307 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3307 17 17, g32p_row03_traceSegment_011_3307_0017, g32p_row03_traceSegment_011_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3341 8 9, g32p_row03_traceSegment_011_3341_0008, g32p_row03_traceSegment_011_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3358 8 9, g32p_row03_traceSegment_011_3358_0008, g32p_row03_traceSegment_011_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3341 17 17, g32p_row03_traceSegment_011_3341_0017, g32p_row03_traceSegment_011_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 3307 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3307 34 34, g32p_row03_traceSegment_011_3307_0034, g32p_row03_traceSegment_011_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 3240 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3240 67 68, g32p_row03_traceSegment_011_3240_0067, g32p_row03_traceSegment_011_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 3375 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3391 8 9, g32p_row03_traceSegment_011_3391_0008, g32p_row03_traceSegment_011_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 3375 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3375 16 17, g32p_row03_traceSegment_011_3375_0016, g32p_row03_traceSegment_011_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3416 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3408 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3408 8 9, g32p_row03_traceSegment_011_3408_0008, g32p_row03_traceSegment_011_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3425 8 9, g32p_row03_traceSegment_011_3425_0008, g32p_row03_traceSegment_011_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3408 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3408 17 17, g32p_row03_traceSegment_011_3408_0017, g32p_row03_traceSegment_011_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 3375 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3375 33 34, g32p_row03_traceSegment_011_3375_0033, g32p_row03_traceSegment_011_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3442 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3442 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3442 8 9, g32p_row03_traceSegment_011_3442_0008, g32p_row03_traceSegment_011_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3459 8 9, g32p_row03_traceSegment_011_3459_0008, g32p_row03_traceSegment_011_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3442 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3442 17 17, g32p_row03_traceSegment_011_3442_0017, g32p_row03_traceSegment_011_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3476 8 9, g32p_row03_traceSegment_011_3476_0008, g32p_row03_traceSegment_011_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3493 8 9, g32p_row03_traceSegment_011_3493_0008, g32p_row03_traceSegment_011_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3476 17 17, g32p_row03_traceSegment_011_3476_0017, g32p_row03_traceSegment_011_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 3442 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3442 34 34, g32p_row03_traceSegment_011_3442_0034, g32p_row03_traceSegment_011_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 3375 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3375 67 68, g32p_row03_traceSegment_011_3375_0067, g32p_row03_traceSegment_011_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 3240 270 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3240 135 135, g32p_row03_traceSegment_011_3240_0135, g32p_row03_traceSegment_011_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3526 8 9, g32p_row03_traceSegment_011_3526_0008, g32p_row03_traceSegment_011_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3510 16 17, g32p_row03_traceSegment_011_3510_0016, g32p_row03_traceSegment_011_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3543 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3543 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3543 8 9, g32p_row03_traceSegment_011_3543_0008, g32p_row03_traceSegment_011_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3560 8 9, g32p_row03_traceSegment_011_3560_0008, g32p_row03_traceSegment_011_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3543 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3543 17 17, g32p_row03_traceSegment_011_3543_0017, g32p_row03_traceSegment_011_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 3510 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3510 33 34, g32p_row03_traceSegment_011_3510_0033, g32p_row03_traceSegment_011_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3577 8 9, g32p_row03_traceSegment_011_3577_0008, g32p_row03_traceSegment_011_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3594 8 9, g32p_row03_traceSegment_011_3594_0008, g32p_row03_traceSegment_011_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3577 17 17, g32p_row03_traceSegment_011_3577_0017, g32p_row03_traceSegment_011_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3619 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3611 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3611 8 9, g32p_row03_traceSegment_011_3611_0008, g32p_row03_traceSegment_011_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3628 8 9, g32p_row03_traceSegment_011_3628_0008, g32p_row03_traceSegment_011_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3611 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3611 17 17, g32p_row03_traceSegment_011_3611_0017, g32p_row03_traceSegment_011_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 3577 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3577 34 34, g32p_row03_traceSegment_011_3577_0034, g32p_row03_traceSegment_011_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 3510 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3510 67 68, g32p_row03_traceSegment_011_3510_0067, g32p_row03_traceSegment_011_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 3645 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3661 8 9, g32p_row03_traceSegment_011_3661_0008, g32p_row03_traceSegment_011_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 3645 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3645 16 17, g32p_row03_traceSegment_011_3645_0016, g32p_row03_traceSegment_011_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3678 8 9, g32p_row03_traceSegment_011_3678_0008, g32p_row03_traceSegment_011_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3703 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3695 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3695 8 9, g32p_row03_traceSegment_011_3695_0008, g32p_row03_traceSegment_011_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3678 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3678 17 17, g32p_row03_traceSegment_011_3678_0017, g32p_row03_traceSegment_011_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 3645 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3645 33 34, g32p_row03_traceSegment_011_3645_0033, g32p_row03_traceSegment_011_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3712 8 9, g32p_row03_traceSegment_011_3712_0008, g32p_row03_traceSegment_011_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3729 8 9, g32p_row03_traceSegment_011_3729_0008, g32p_row03_traceSegment_011_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3712 17 17, g32p_row03_traceSegment_011_3712_0017, g32p_row03_traceSegment_011_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3754 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3746 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3746 8 9, g32p_row03_traceSegment_011_3746_0008, g32p_row03_traceSegment_011_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3763 8 9, g32p_row03_traceSegment_011_3763_0008, g32p_row03_traceSegment_011_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3746 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3746 17 17, g32p_row03_traceSegment_011_3746_0017, g32p_row03_traceSegment_011_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 3712 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3712 34 34, g32p_row03_traceSegment_011_3712_0034, g32p_row03_traceSegment_011_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 3645 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3645 67 68, g32p_row03_traceSegment_011_3645_0067, g32p_row03_traceSegment_011_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 3510 270 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3510 135 135, g32p_row03_traceSegment_011_3510_0135, g32p_row03_traceSegment_011_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_011 3240 540 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3240 270 270, g32p_row03_traceSegment_011_3240_0270, g32p_row03_traceSegment_011_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3804 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3796 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3796 8 9, g32p_row03_traceSegment_011_3796_0008, g32p_row03_traceSegment_011_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 3780 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3780 16 17, g32p_row03_traceSegment_011_3780_0016, g32p_row03_traceSegment_011_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3813 8 9, g32p_row03_traceSegment_011_3813_0008, g32p_row03_traceSegment_011_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3830 8 9, g32p_row03_traceSegment_011_3830_0008, g32p_row03_traceSegment_011_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3813 17 17, g32p_row03_traceSegment_011_3813_0017, g32p_row03_traceSegment_011_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 3780 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3780 33 34, g32p_row03_traceSegment_011_3780_0033, g32p_row03_traceSegment_011_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3847 8 9, g32p_row03_traceSegment_011_3847_0008, g32p_row03_traceSegment_011_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3864 8 9, g32p_row03_traceSegment_011_3864_0008, g32p_row03_traceSegment_011_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3847 17 17, g32p_row03_traceSegment_011_3847_0017, g32p_row03_traceSegment_011_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3881 8 9, g32p_row03_traceSegment_011_3881_0008, g32p_row03_traceSegment_011_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3898 8 9, g32p_row03_traceSegment_011_3898_0008, g32p_row03_traceSegment_011_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3881 17 17, g32p_row03_traceSegment_011_3881_0017, g32p_row03_traceSegment_011_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3847 34 34, g32p_row03_traceSegment_011_3847_0034, g32p_row03_traceSegment_011_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 3780 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3780 67 68, g32p_row03_traceSegment_011_3780_0067, g32p_row03_traceSegment_011_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3931 8 9, g32p_row03_traceSegment_011_3931_0008, g32p_row03_traceSegment_011_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3915 16 17, g32p_row03_traceSegment_011_3915_0016, g32p_row03_traceSegment_011_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3948 8 9, g32p_row03_traceSegment_011_3948_0008, g32p_row03_traceSegment_011_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3965 8 9, g32p_row03_traceSegment_011_3965_0008, g32p_row03_traceSegment_011_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3948 17 17, g32p_row03_traceSegment_011_3948_0017, g32p_row03_traceSegment_011_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3915 33 34, g32p_row03_traceSegment_011_3915_0033, g32p_row03_traceSegment_011_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3982 8 9, g32p_row03_traceSegment_011_3982_0008, g32p_row03_traceSegment_011_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3999 8 9, g32p_row03_traceSegment_011_3999_0008, g32p_row03_traceSegment_011_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3982 17 17, g32p_row03_traceSegment_011_3982_0017, g32p_row03_traceSegment_011_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4016 8 9, g32p_row03_traceSegment_011_4016_0008, g32p_row03_traceSegment_011_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4033 8 9, g32p_row03_traceSegment_011_4033_0008, g32p_row03_traceSegment_011_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4016 17 17, g32p_row03_traceSegment_011_4016_0017, g32p_row03_traceSegment_011_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3982 34 34, g32p_row03_traceSegment_011_3982_0034, g32p_row03_traceSegment_011_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3915 67 68, g32p_row03_traceSegment_011_3915_0067, g32p_row03_traceSegment_011_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 3780 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3780 135 135, g32p_row03_traceSegment_011_3780_0135, g32p_row03_traceSegment_011_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4066 8 9, g32p_row03_traceSegment_011_4066_0008, g32p_row03_traceSegment_011_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4050 16 17, g32p_row03_traceSegment_011_4050_0016, g32p_row03_traceSegment_011_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4083 8 9, g32p_row03_traceSegment_011_4083_0008, g32p_row03_traceSegment_011_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4100 8 9, g32p_row03_traceSegment_011_4100_0008, g32p_row03_traceSegment_011_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4083 17 17, g32p_row03_traceSegment_011_4083_0017, g32p_row03_traceSegment_011_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4050 33 34, g32p_row03_traceSegment_011_4050_0033, g32p_row03_traceSegment_011_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4117 8 9, g32p_row03_traceSegment_011_4117_0008, g32p_row03_traceSegment_011_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4134 8 9, g32p_row03_traceSegment_011_4134_0008, g32p_row03_traceSegment_011_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4117 17 17, g32p_row03_traceSegment_011_4117_0017, g32p_row03_traceSegment_011_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4151 8 9, g32p_row03_traceSegment_011_4151_0008, g32p_row03_traceSegment_011_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4168 8 9, g32p_row03_traceSegment_011_4168_0008, g32p_row03_traceSegment_011_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4151 17 17, g32p_row03_traceSegment_011_4151_0017, g32p_row03_traceSegment_011_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4117 34 34, g32p_row03_traceSegment_011_4117_0034, g32p_row03_traceSegment_011_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4050 67 68, g32p_row03_traceSegment_011_4050_0067, g32p_row03_traceSegment_011_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_011 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4201 8 9, g32p_row03_traceSegment_011_4201_0008, g32p_row03_traceSegment_011_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_011 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4185 16 17, g32p_row03_traceSegment_011_4185_0016, g32p_row03_traceSegment_011_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4218 8 9, g32p_row03_traceSegment_011_4218_0008, g32p_row03_traceSegment_011_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4235 8 9, g32p_row03_traceSegment_011_4235_0008, g32p_row03_traceSegment_011_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4218 17 17, g32p_row03_traceSegment_011_4218_0017, g32p_row03_traceSegment_011_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_011 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4185 33 34, g32p_row03_traceSegment_011_4185_0033, g32p_row03_traceSegment_011_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4252 8 9, g32p_row03_traceSegment_011_4252_0008, g32p_row03_traceSegment_011_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4269 8 9, g32p_row03_traceSegment_011_4269_0008, g32p_row03_traceSegment_011_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4252 17 17, g32p_row03_traceSegment_011_4252_0017, g32p_row03_traceSegment_011_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4286 8 9, g32p_row03_traceSegment_011_4286_0008, g32p_row03_traceSegment_011_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_011 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_011 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_011_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_011 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4303 8 9, g32p_row03_traceSegment_011_4303_0008, g32p_row03_traceSegment_011_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_011 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4286 17 17, g32p_row03_traceSegment_011_4286_0017, g32p_row03_traceSegment_011_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_011 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4252 34 34, g32p_row03_traceSegment_011_4252_0034, g32p_row03_traceSegment_011_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_011 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4185 67 68, g32p_row03_traceSegment_011_4185_0067, g32p_row03_traceSegment_011_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_011_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_011 4050 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 4050 135 135, g32p_row03_traceSegment_011_4050_0135, g32p_row03_traceSegment_011_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_011 3780 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3780 270 270, g32p_row03_traceSegment_011_3780_0270, g32p_row03_traceSegment_011_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_011_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_011 3240 1080 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 3240 540 540, g32p_row03_traceSegment_011_3240_0540, g32p_row03_traceSegment_011_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_011_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_011 2160 2160 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 2160 1080 1080, g32p_row03_traceSegment_011_2160_1080, g32p_row03_traceSegment_011_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_011_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_011 0 4320 = [0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_011 0 2160 2160, g32p_row03_traceSegment_011_0000_2160, g32p_row03_traceSegment_011_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 11 = [0, 0, 40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_011_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_013 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 13 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_013_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 16 8 9, g32p_row03_traceSegment_013_0016_0008, g32p_row03_traceSegment_013_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 0 16 17, g32p_row03_traceSegment_013_0000_0016, g32p_row03_traceSegment_013_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 33 8 9, g32p_row03_traceSegment_013_0033_0008, g32p_row03_traceSegment_013_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 50 8 9, g32p_row03_traceSegment_013_0050_0008, g32p_row03_traceSegment_013_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 33 17 17, g32p_row03_traceSegment_013_0033_0017, g32p_row03_traceSegment_013_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 0 33 34, g32p_row03_traceSegment_013_0000_0033, g32p_row03_traceSegment_013_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 75 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 67 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 67 8 9, g32p_row03_traceSegment_013_0067_0008, g32p_row03_traceSegment_013_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 92 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 84 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 84 8 9, g32p_row03_traceSegment_013_0084_0008, g32p_row03_traceSegment_013_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 67 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 67 17 17, g32p_row03_traceSegment_013_0067_0017, g32p_row03_traceSegment_013_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 101 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 109 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 101 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 101 8 9, g32p_row03_traceSegment_013_0101_0008, g32p_row03_traceSegment_013_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 118 8 9, g32p_row03_traceSegment_013_0118_0008, g32p_row03_traceSegment_013_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 101 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 101 17 17, g32p_row03_traceSegment_013_0101_0017, g32p_row03_traceSegment_013_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 67 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 67 34 34, g32p_row03_traceSegment_013_0067_0034, g32p_row03_traceSegment_013_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 0 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 0 67 68, g32p_row03_traceSegment_013_0000_0067, g32p_row03_traceSegment_013_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 151 8 9, g32p_row03_traceSegment_013_0151_0008, g32p_row03_traceSegment_013_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 135 16 17, g32p_row03_traceSegment_013_0135_0016, g32p_row03_traceSegment_013_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 168 8 9, g32p_row03_traceSegment_013_0168_0008, g32p_row03_traceSegment_013_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 185 8 9, g32p_row03_traceSegment_013_0185_0008, g32p_row03_traceSegment_013_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 168 17 17, g32p_row03_traceSegment_013_0168_0017, g32p_row03_traceSegment_013_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 135 33 34, g32p_row03_traceSegment_013_0135_0033, g32p_row03_traceSegment_013_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 202 8 9, g32p_row03_traceSegment_013_0202_0008, g32p_row03_traceSegment_013_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 219 8 9, g32p_row03_traceSegment_013_0219_0008, g32p_row03_traceSegment_013_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 202 17 17, g32p_row03_traceSegment_013_0202_0017, g32p_row03_traceSegment_013_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 236 8 9, g32p_row03_traceSegment_013_0236_0008, g32p_row03_traceSegment_013_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 253 8 9, g32p_row03_traceSegment_013_0253_0008, g32p_row03_traceSegment_013_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 236 17 17, g32p_row03_traceSegment_013_0236_0017, g32p_row03_traceSegment_013_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 202 34 34, g32p_row03_traceSegment_013_0202_0034, g32p_row03_traceSegment_013_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 135 67 68, g32p_row03_traceSegment_013_0135_0067, g32p_row03_traceSegment_013_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 0 270 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 0 135 135, g32p_row03_traceSegment_013_0000_0135, g32p_row03_traceSegment_013_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 286 8 9, g32p_row03_traceSegment_013_0286_0008, g32p_row03_traceSegment_013_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 270 16 17, g32p_row03_traceSegment_013_0270_0016, g32p_row03_traceSegment_013_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 303 8 9, g32p_row03_traceSegment_013_0303_0008, g32p_row03_traceSegment_013_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 320 8 9, g32p_row03_traceSegment_013_0320_0008, g32p_row03_traceSegment_013_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 303 17 17, g32p_row03_traceSegment_013_0303_0017, g32p_row03_traceSegment_013_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 270 33 34, g32p_row03_traceSegment_013_0270_0033, g32p_row03_traceSegment_013_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 337 8 9, g32p_row03_traceSegment_013_0337_0008, g32p_row03_traceSegment_013_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 354 8 9, g32p_row03_traceSegment_013_0354_0008, g32p_row03_traceSegment_013_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 337 17 17, g32p_row03_traceSegment_013_0337_0017, g32p_row03_traceSegment_013_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 371 8 9, g32p_row03_traceSegment_013_0371_0008, g32p_row03_traceSegment_013_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 388 8 9, g32p_row03_traceSegment_013_0388_0008, g32p_row03_traceSegment_013_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 371 17 17, g32p_row03_traceSegment_013_0371_0017, g32p_row03_traceSegment_013_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 337 34 34, g32p_row03_traceSegment_013_0337_0034, g32p_row03_traceSegment_013_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 270 67 68, g32p_row03_traceSegment_013_0270_0067, g32p_row03_traceSegment_013_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 421 8 9, g32p_row03_traceSegment_013_0421_0008, g32p_row03_traceSegment_013_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 405 16 17, g32p_row03_traceSegment_013_0405_0016, g32p_row03_traceSegment_013_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 438 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 438 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 438 8 9, g32p_row03_traceSegment_013_0438_0008, g32p_row03_traceSegment_013_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 455 8 9, g32p_row03_traceSegment_013_0455_0008, g32p_row03_traceSegment_013_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 438 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 438 17 17, g32p_row03_traceSegment_013_0438_0017, g32p_row03_traceSegment_013_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 405 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 405 33 34, g32p_row03_traceSegment_013_0405_0033, g32p_row03_traceSegment_013_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 472 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 472 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 472 8 9, g32p_row03_traceSegment_013_0472_0008, g32p_row03_traceSegment_013_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 497 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 489 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 489 8 9, g32p_row03_traceSegment_013_0489_0008, g32p_row03_traceSegment_013_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 472 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 472 17 17, g32p_row03_traceSegment_013_0472_0017, g32p_row03_traceSegment_013_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 506 8 9, g32p_row03_traceSegment_013_0506_0008, g32p_row03_traceSegment_013_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 531 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 523 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 523 8 9, g32p_row03_traceSegment_013_0523_0008, g32p_row03_traceSegment_013_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 506 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 506 17 17, g32p_row03_traceSegment_013_0506_0017, g32p_row03_traceSegment_013_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 472 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 472 34 34, g32p_row03_traceSegment_013_0472_0034, g32p_row03_traceSegment_013_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 405 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 405 67 68, g32p_row03_traceSegment_013_0405_0067, g32p_row03_traceSegment_013_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 270 270 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 270 135 135, g32p_row03_traceSegment_013_0270_0135, g32p_row03_traceSegment_013_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_013 0 540 = [0, 0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 0 270 270, g32p_row03_traceSegment_013_0000_0270, g32p_row03_traceSegment_013_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 540 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 556 8 9, g32p_row03_traceSegment_013_0556_0008, g32p_row03_traceSegment_013_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 540 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 540 16 17, g32p_row03_traceSegment_013_0540_0016, g32p_row03_traceSegment_013_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 573 8 9, g32p_row03_traceSegment_013_0573_0008, g32p_row03_traceSegment_013_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 590 8 9, g32p_row03_traceSegment_013_0590_0008, g32p_row03_traceSegment_013_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 573 17 17, g32p_row03_traceSegment_013_0573_0017, g32p_row03_traceSegment_013_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 540 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 540 33 34, g32p_row03_traceSegment_013_0540_0033, g32p_row03_traceSegment_013_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 607 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 607 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 607 8 9, g32p_row03_traceSegment_013_0607_0008, g32p_row03_traceSegment_013_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 632 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 624 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 624 8 9, g32p_row03_traceSegment_013_0624_0008, g32p_row03_traceSegment_013_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 607 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 607 17 17, g32p_row03_traceSegment_013_0607_0017, g32p_row03_traceSegment_013_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 641 8 9, g32p_row03_traceSegment_013_0641_0008, g32p_row03_traceSegment_013_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 666 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 658 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 658 8 9, g32p_row03_traceSegment_013_0658_0008, g32p_row03_traceSegment_013_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 641 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 641 17 17, g32p_row03_traceSegment_013_0641_0017, g32p_row03_traceSegment_013_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 607 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 607 34 34, g32p_row03_traceSegment_013_0607_0034, g32p_row03_traceSegment_013_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 540 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 540 67 68, g32p_row03_traceSegment_013_0540_0067, g32p_row03_traceSegment_013_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 691 8 9, g32p_row03_traceSegment_013_0691_0008, g32p_row03_traceSegment_013_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 675 16 17, g32p_row03_traceSegment_013_0675_0016, g32p_row03_traceSegment_013_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 708 8 9, g32p_row03_traceSegment_013_0708_0008, g32p_row03_traceSegment_013_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 725 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 725 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 725 8 9, g32p_row03_traceSegment_013_0725_0008, g32p_row03_traceSegment_013_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 708 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 708 17 17, g32p_row03_traceSegment_013_0708_0017, g32p_row03_traceSegment_013_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 675 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 675 33 34, g32p_row03_traceSegment_013_0675_0033, g32p_row03_traceSegment_013_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 750 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 742 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 742 8 9, g32p_row03_traceSegment_013_0742_0008, g32p_row03_traceSegment_013_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 759 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 767 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 759 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 759 8 9, g32p_row03_traceSegment_013_0759_0008, g32p_row03_traceSegment_013_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 742 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 742 17 17, g32p_row03_traceSegment_013_0742_0017, g32p_row03_traceSegment_013_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 784 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 776 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 776 8 9, g32p_row03_traceSegment_013_0776_0008, g32p_row03_traceSegment_013_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 801 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 793 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 793 8 9, g32p_row03_traceSegment_013_0793_0008, g32p_row03_traceSegment_013_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 776 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 776 17 17, g32p_row03_traceSegment_013_0776_0017, g32p_row03_traceSegment_013_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 742 68 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 742 34 34, g32p_row03_traceSegment_013_0742_0034, g32p_row03_traceSegment_013_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 675 135 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 675 67 68, g32p_row03_traceSegment_013_0675_0067, g32p_row03_traceSegment_013_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 540 270 = [0, 0, 7, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 540 135 135, g32p_row03_traceSegment_013_0540_0135, g32p_row03_traceSegment_013_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 810 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 826 8 9, g32p_row03_traceSegment_013_0826_0008, g32p_row03_traceSegment_013_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 810 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 810 16 17, g32p_row03_traceSegment_013_0810_0016, g32p_row03_traceSegment_013_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 851 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 843 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 843 8 9, g32p_row03_traceSegment_013_0843_0008, g32p_row03_traceSegment_013_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 868 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 860 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 860 8 9, g32p_row03_traceSegment_013_0860_0008, g32p_row03_traceSegment_013_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 843 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 843 17 17, g32p_row03_traceSegment_013_0843_0017, g32p_row03_traceSegment_013_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 810 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 810 33 34, g32p_row03_traceSegment_013_0810_0033, g32p_row03_traceSegment_013_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 885 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 877 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 877 8 9, g32p_row03_traceSegment_013_0877_0008, g32p_row03_traceSegment_013_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 902 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 894 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 894 8 9, g32p_row03_traceSegment_013_0894_0008, g32p_row03_traceSegment_013_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 877 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 877 17 17, g32p_row03_traceSegment_013_0877_0017, g32p_row03_traceSegment_013_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 911 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 911 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 911 8 9, g32p_row03_traceSegment_013_0911_0008, g32p_row03_traceSegment_013_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 928 8 9, g32p_row03_traceSegment_013_0928_0008, g32p_row03_traceSegment_013_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 911 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 911 17 17, g32p_row03_traceSegment_013_0911_0017, g32p_row03_traceSegment_013_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 877 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 877 34 34, g32p_row03_traceSegment_013_0877_0034, g32p_row03_traceSegment_013_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 810 135 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 810 67 68, g32p_row03_traceSegment_013_0810_0067, g32p_row03_traceSegment_013_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 961 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 961 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 961 8 9, g32p_row03_traceSegment_013_0961_0008, g32p_row03_traceSegment_013_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 945 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 945 16 17, g32p_row03_traceSegment_013_0945_0016, g32p_row03_traceSegment_013_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 978 8 9, g32p_row03_traceSegment_013_0978_0008, g32p_row03_traceSegment_013_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 995 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 995 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 995 8 9, g32p_row03_traceSegment_013_0995_0008, g32p_row03_traceSegment_013_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 978 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 978 17 17, g32p_row03_traceSegment_013_0978_0017, g32p_row03_traceSegment_013_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 945 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 945 33 34, g32p_row03_traceSegment_013_0945_0033, g32p_row03_traceSegment_013_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1012 8 9, g32p_row03_traceSegment_013_1012_0008, g32p_row03_traceSegment_013_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1029 8 9, g32p_row03_traceSegment_013_1029_0008, g32p_row03_traceSegment_013_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1012 17 17, g32p_row03_traceSegment_013_1012_0017, g32p_row03_traceSegment_013_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1046 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1046 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1046 8 9, g32p_row03_traceSegment_013_1046_0008, g32p_row03_traceSegment_013_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1071 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1063 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1063 8 9, g32p_row03_traceSegment_013_1063_0008, g32p_row03_traceSegment_013_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1046 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1046 17 17, g32p_row03_traceSegment_013_1046_0017, g32p_row03_traceSegment_013_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 1012 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1012 34 34, g32p_row03_traceSegment_013_1012_0034, g32p_row03_traceSegment_013_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 945 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 945 67 68, g32p_row03_traceSegment_013_0945_0067, g32p_row03_traceSegment_013_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 810 270 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 810 135 135, g32p_row03_traceSegment_013_0810_0135, g32p_row03_traceSegment_013_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_013 540 540 = [0, 0, 19, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 540 270 270, g32p_row03_traceSegment_013_0540_0270, g32p_row03_traceSegment_013_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_013 0 1080 = [0, 0, 23, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 0 540 540, g32p_row03_traceSegment_013_0000_0540, g32p_row03_traceSegment_013_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 1080 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1096 8 9, g32p_row03_traceSegment_013_1096_0008, g32p_row03_traceSegment_013_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 1080 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1080 16 17, g32p_row03_traceSegment_013_1080_0016, g32p_row03_traceSegment_013_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1113 8 9, g32p_row03_traceSegment_013_1113_0008, g32p_row03_traceSegment_013_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1130 8 9, g32p_row03_traceSegment_013_1130_0008, g32p_row03_traceSegment_013_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1113 17 17, g32p_row03_traceSegment_013_1113_0017, g32p_row03_traceSegment_013_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 1080 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1080 33 34, g32p_row03_traceSegment_013_1080_0033, g32p_row03_traceSegment_013_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1147 8 9, g32p_row03_traceSegment_013_1147_0008, g32p_row03_traceSegment_013_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1164 8 9, g32p_row03_traceSegment_013_1164_0008, g32p_row03_traceSegment_013_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1147 17 17, g32p_row03_traceSegment_013_1147_0017, g32p_row03_traceSegment_013_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1181 8 9, g32p_row03_traceSegment_013_1181_0008, g32p_row03_traceSegment_013_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1198 8 9, g32p_row03_traceSegment_013_1198_0008, g32p_row03_traceSegment_013_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1181 17 17, g32p_row03_traceSegment_013_1181_0017, g32p_row03_traceSegment_013_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1147 34 34, g32p_row03_traceSegment_013_1147_0034, g32p_row03_traceSegment_013_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 1080 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1080 67 68, g32p_row03_traceSegment_013_1080_0067, g32p_row03_traceSegment_013_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1231 8 9, g32p_row03_traceSegment_013_1231_0008, g32p_row03_traceSegment_013_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1215 16 17, g32p_row03_traceSegment_013_1215_0016, g32p_row03_traceSegment_013_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1248 8 9, g32p_row03_traceSegment_013_1248_0008, g32p_row03_traceSegment_013_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1265 8 9, g32p_row03_traceSegment_013_1265_0008, g32p_row03_traceSegment_013_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1248 17 17, g32p_row03_traceSegment_013_1248_0017, g32p_row03_traceSegment_013_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1215 33 34, g32p_row03_traceSegment_013_1215_0033, g32p_row03_traceSegment_013_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1282 8 9, g32p_row03_traceSegment_013_1282_0008, g32p_row03_traceSegment_013_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1299 8 9, g32p_row03_traceSegment_013_1299_0008, g32p_row03_traceSegment_013_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1282 17 17, g32p_row03_traceSegment_013_1282_0017, g32p_row03_traceSegment_013_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1316 8 9, g32p_row03_traceSegment_013_1316_0008, g32p_row03_traceSegment_013_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1333 8 9, g32p_row03_traceSegment_013_1333_0008, g32p_row03_traceSegment_013_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1316 17 17, g32p_row03_traceSegment_013_1316_0017, g32p_row03_traceSegment_013_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1282 34 34, g32p_row03_traceSegment_013_1282_0034, g32p_row03_traceSegment_013_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1215 67 68, g32p_row03_traceSegment_013_1215_0067, g32p_row03_traceSegment_013_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 1080 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1080 135 135, g32p_row03_traceSegment_013_1080_0135, g32p_row03_traceSegment_013_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1366 8 9, g32p_row03_traceSegment_013_1366_0008, g32p_row03_traceSegment_013_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1350 16 17, g32p_row03_traceSegment_013_1350_0016, g32p_row03_traceSegment_013_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1383 8 9, g32p_row03_traceSegment_013_1383_0008, g32p_row03_traceSegment_013_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1400 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1400 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1400 8 9, g32p_row03_traceSegment_013_1400_0008, g32p_row03_traceSegment_013_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1383 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1383 17 17, g32p_row03_traceSegment_013_1383_0017, g32p_row03_traceSegment_013_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 1350 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1350 33 34, g32p_row03_traceSegment_013_1350_0033, g32p_row03_traceSegment_013_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1417 8 9, g32p_row03_traceSegment_013_1417_0008, g32p_row03_traceSegment_013_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1434 8 9, g32p_row03_traceSegment_013_1434_0008, g32p_row03_traceSegment_013_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1417 17 17, g32p_row03_traceSegment_013_1417_0017, g32p_row03_traceSegment_013_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1451 8 9, g32p_row03_traceSegment_013_1451_0008, g32p_row03_traceSegment_013_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1468 8 9, g32p_row03_traceSegment_013_1468_0008, g32p_row03_traceSegment_013_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1451 17 17, g32p_row03_traceSegment_013_1451_0017, g32p_row03_traceSegment_013_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1417 34 34, g32p_row03_traceSegment_013_1417_0034, g32p_row03_traceSegment_013_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 1350 135 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1350 67 68, g32p_row03_traceSegment_013_1350_0067, g32p_row03_traceSegment_013_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 1485 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1501 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1509 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1501 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1501 8 9, g32p_row03_traceSegment_013_1501_0008, g32p_row03_traceSegment_013_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 1485 33 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1485 16 17, g32p_row03_traceSegment_013_1485_0016, g32p_row03_traceSegment_013_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1518 8 9, g32p_row03_traceSegment_013_1518_0008, g32p_row03_traceSegment_013_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1535 8 9, g32p_row03_traceSegment_013_1535_0008, g32p_row03_traceSegment_013_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1518 17 17, g32p_row03_traceSegment_013_1518_0017, g32p_row03_traceSegment_013_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 1485 67 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1485 33 34, g32p_row03_traceSegment_013_1485_0033, g32p_row03_traceSegment_013_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1552 8 9, g32p_row03_traceSegment_013_1552_0008, g32p_row03_traceSegment_013_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1569 8 9, g32p_row03_traceSegment_013_1569_0008, g32p_row03_traceSegment_013_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1552 17 17, g32p_row03_traceSegment_013_1552_0017, g32p_row03_traceSegment_013_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1586 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1586 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1586 8 9, g32p_row03_traceSegment_013_1586_0008, g32p_row03_traceSegment_013_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1603 8 9, g32p_row03_traceSegment_013_1603_0008, g32p_row03_traceSegment_013_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1586 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1586 17 17, g32p_row03_traceSegment_013_1586_0017, g32p_row03_traceSegment_013_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 1552 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1552 34 34, g32p_row03_traceSegment_013_1552_0034, g32p_row03_traceSegment_013_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 1485 135 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1485 67 68, g32p_row03_traceSegment_013_1485_0067, g32p_row03_traceSegment_013_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 1350 270 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1350 135 135, g32p_row03_traceSegment_013_1350_0135, g32p_row03_traceSegment_013_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_013 1080 540 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1080 270 270, g32p_row03_traceSegment_013_1080_0270, g32p_row03_traceSegment_013_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1644 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1636 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1636 8 9, g32p_row03_traceSegment_013_1636_0008, g32p_row03_traceSegment_013_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 1620 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1620 16 17, g32p_row03_traceSegment_013_1620_0016, g32p_row03_traceSegment_013_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1661 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1653 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1653 8 9, g32p_row03_traceSegment_013_1653_0008, g32p_row03_traceSegment_013_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1670 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1670 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1670 8 9, g32p_row03_traceSegment_013_1670_0008, g32p_row03_traceSegment_013_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1653 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1653 17 17, g32p_row03_traceSegment_013_1653_0017, g32p_row03_traceSegment_013_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 1620 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1620 33 34, g32p_row03_traceSegment_013_1620_0033, g32p_row03_traceSegment_013_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1687 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1687 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1687 8 9, g32p_row03_traceSegment_013_1687_0008, g32p_row03_traceSegment_013_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1704 8 9, g32p_row03_traceSegment_013_1704_0008, g32p_row03_traceSegment_013_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1687 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1687 17 17, g32p_row03_traceSegment_013_1687_0017, g32p_row03_traceSegment_013_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1721 8 9, g32p_row03_traceSegment_013_1721_0008, g32p_row03_traceSegment_013_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1738 8 9, g32p_row03_traceSegment_013_1738_0008, g32p_row03_traceSegment_013_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1721 17 17, g32p_row03_traceSegment_013_1721_0017, g32p_row03_traceSegment_013_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 1687 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1687 34 34, g32p_row03_traceSegment_013_1687_0034, g32p_row03_traceSegment_013_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 1620 135 = [0, 0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1620 67 68, g32p_row03_traceSegment_013_1620_0067, g32p_row03_traceSegment_013_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 1755 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1771 8 9, g32p_row03_traceSegment_013_1771_0008, g32p_row03_traceSegment_013_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 1755 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1755 16 17, g32p_row03_traceSegment_013_1755_0016, g32p_row03_traceSegment_013_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1788 8 9, g32p_row03_traceSegment_013_1788_0008, g32p_row03_traceSegment_013_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1813 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1805 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1805 8 9, g32p_row03_traceSegment_013_1805_0008, g32p_row03_traceSegment_013_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1788 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1788 17 17, g32p_row03_traceSegment_013_1788_0017, g32p_row03_traceSegment_013_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 1755 67 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1755 33 34, g32p_row03_traceSegment_013_1755_0033, g32p_row03_traceSegment_013_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1822 8 9, g32p_row03_traceSegment_013_1822_0008, g32p_row03_traceSegment_013_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1839 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1839 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1839 8 9, g32p_row03_traceSegment_013_1839_0008, g32p_row03_traceSegment_013_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1822 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1822 17 17, g32p_row03_traceSegment_013_1822_0017, g32p_row03_traceSegment_013_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1856 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1856 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1856 8 9, g32p_row03_traceSegment_013_1856_0008, g32p_row03_traceSegment_013_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1873 8 9, g32p_row03_traceSegment_013_1873_0008, g32p_row03_traceSegment_013_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1856 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1856 17 17, g32p_row03_traceSegment_013_1856_0017, g32p_row03_traceSegment_013_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 1822 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1822 34 34, g32p_row03_traceSegment_013_1822_0034, g32p_row03_traceSegment_013_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 1755 135 = [0, 0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1755 67 68, g32p_row03_traceSegment_013_1755_0067, g32p_row03_traceSegment_013_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 1620 270 = [0, 0, 8, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1620 135 135, g32p_row03_traceSegment_013_1620_0135, g32p_row03_traceSegment_013_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 1890 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1906 8 9, g32p_row03_traceSegment_013_1906_0008, g32p_row03_traceSegment_013_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 1890 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1890 16 17, g32p_row03_traceSegment_013_1890_0016, g32p_row03_traceSegment_013_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1931 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1923 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1923 8 9, g32p_row03_traceSegment_013_1923_0008, g32p_row03_traceSegment_013_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1940 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1948 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1940 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1940 8 9, g32p_row03_traceSegment_013_1940_0008, g32p_row03_traceSegment_013_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1923 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1923 17 17, g32p_row03_traceSegment_013_1923_0017, g32p_row03_traceSegment_013_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 1890 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1890 33 34, g32p_row03_traceSegment_013_1890_0033, g32p_row03_traceSegment_013_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1957 8 9, g32p_row03_traceSegment_013_1957_0008, g32p_row03_traceSegment_013_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1974 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1982 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1974 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1974 8 9, g32p_row03_traceSegment_013_1974_0008, g32p_row03_traceSegment_013_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1957 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1957 17 17, g32p_row03_traceSegment_013_1957_0017, g32p_row03_traceSegment_013_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1991 8 9, g32p_row03_traceSegment_013_1991_0008, g32p_row03_traceSegment_013_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2008 8 9, g32p_row03_traceSegment_013_2008_0008, g32p_row03_traceSegment_013_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1991 17 17, g32p_row03_traceSegment_013_1991_0017, g32p_row03_traceSegment_013_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 1957 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1957 34 34, g32p_row03_traceSegment_013_1957_0034, g32p_row03_traceSegment_013_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 1890 135 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1890 67 68, g32p_row03_traceSegment_013_1890_0067, g32p_row03_traceSegment_013_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2041 8 9, g32p_row03_traceSegment_013_2041_0008, g32p_row03_traceSegment_013_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2025 16 17, g32p_row03_traceSegment_013_2025_0016, g32p_row03_traceSegment_013_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2058 8 9, g32p_row03_traceSegment_013_2058_0008, g32p_row03_traceSegment_013_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2075 8 9, g32p_row03_traceSegment_013_2075_0008, g32p_row03_traceSegment_013_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2058 17 17, g32p_row03_traceSegment_013_2058_0017, g32p_row03_traceSegment_013_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2025 33 34, g32p_row03_traceSegment_013_2025_0033, g32p_row03_traceSegment_013_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2100 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2092 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2092 8 9, g32p_row03_traceSegment_013_2092_0008, g32p_row03_traceSegment_013_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2109 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2109 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2109 8 9, g32p_row03_traceSegment_013_2109_0008, g32p_row03_traceSegment_013_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2092 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2092 17 17, g32p_row03_traceSegment_013_2092_0017, g32p_row03_traceSegment_013_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2134 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2126 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2126 8 9, g32p_row03_traceSegment_013_2126_0008, g32p_row03_traceSegment_013_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2143 8 9, g32p_row03_traceSegment_013_2143_0008, g32p_row03_traceSegment_013_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2126 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2126 17 17, g32p_row03_traceSegment_013_2126_0017, g32p_row03_traceSegment_013_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 2092 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2092 34 34, g32p_row03_traceSegment_013_2092_0034, g32p_row03_traceSegment_013_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 2025 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2025 67 68, g32p_row03_traceSegment_013_2025_0067, g32p_row03_traceSegment_013_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 1890 270 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1890 135 135, g32p_row03_traceSegment_013_1890_0135, g32p_row03_traceSegment_013_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_013 1620 540 = [0, 0, 17, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1620 270 270, g32p_row03_traceSegment_013_1620_0270, g32p_row03_traceSegment_013_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_013_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_013 1080 1080 = [0, 0, 20, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 1080 540 540, g32p_row03_traceSegment_013_1080_0540, g32p_row03_traceSegment_013_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_013 0 2160 = [0, 0, 43, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 0 1080 1080, g32p_row03_traceSegment_013_0000_1080, g32p_row03_traceSegment_013_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2176 8 9, g32p_row03_traceSegment_013_2176_0008, g32p_row03_traceSegment_013_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2160 16 17, g32p_row03_traceSegment_013_2160_0016, g32p_row03_traceSegment_013_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2193 8 9, g32p_row03_traceSegment_013_2193_0008, g32p_row03_traceSegment_013_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2210 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2210 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2210 8 9, g32p_row03_traceSegment_013_2210_0008, g32p_row03_traceSegment_013_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2193 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2193 17 17, g32p_row03_traceSegment_013_2193_0017, g32p_row03_traceSegment_013_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 2160 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2160 33 34, g32p_row03_traceSegment_013_2160_0033, g32p_row03_traceSegment_013_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2227 8 9, g32p_row03_traceSegment_013_2227_0008, g32p_row03_traceSegment_013_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2252 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2244 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2244 8 9, g32p_row03_traceSegment_013_2244_0008, g32p_row03_traceSegment_013_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2227 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2227 17 17, g32p_row03_traceSegment_013_2227_0017, g32p_row03_traceSegment_013_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2261 8 9, g32p_row03_traceSegment_013_2261_0008, g32p_row03_traceSegment_013_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2278 8 9, g32p_row03_traceSegment_013_2278_0008, g32p_row03_traceSegment_013_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2261 17 17, g32p_row03_traceSegment_013_2261_0017, g32p_row03_traceSegment_013_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 2227 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2227 34 34, g32p_row03_traceSegment_013_2227_0034, g32p_row03_traceSegment_013_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 2160 135 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2160 67 68, g32p_row03_traceSegment_013_2160_0067, g32p_row03_traceSegment_013_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 2295 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2311 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2311 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2311 8 9, g32p_row03_traceSegment_013_2311_0008, g32p_row03_traceSegment_013_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 2295 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2295 16 17, g32p_row03_traceSegment_013_2295_0016, g32p_row03_traceSegment_013_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2328 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2328 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2328 8 9, g32p_row03_traceSegment_013_2328_0008, g32p_row03_traceSegment_013_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2345 8 9, g32p_row03_traceSegment_013_2345_0008, g32p_row03_traceSegment_013_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2328 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2328 17 17, g32p_row03_traceSegment_013_2328_0017, g32p_row03_traceSegment_013_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 2295 67 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2295 33 34, g32p_row03_traceSegment_013_2295_0033, g32p_row03_traceSegment_013_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2362 8 9, g32p_row03_traceSegment_013_2362_0008, g32p_row03_traceSegment_013_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2387 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2379 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2379 8 9, g32p_row03_traceSegment_013_2379_0008, g32p_row03_traceSegment_013_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2362 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2362 17 17, g32p_row03_traceSegment_013_2362_0017, g32p_row03_traceSegment_013_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2396 8 9, g32p_row03_traceSegment_013_2396_0008, g32p_row03_traceSegment_013_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2413 8 9, g32p_row03_traceSegment_013_2413_0008, g32p_row03_traceSegment_013_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2396 17 17, g32p_row03_traceSegment_013_2396_0017, g32p_row03_traceSegment_013_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 2362 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2362 34 34, g32p_row03_traceSegment_013_2362_0034, g32p_row03_traceSegment_013_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 2295 135 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2295 67 68, g32p_row03_traceSegment_013_2295_0067, g32p_row03_traceSegment_013_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 2160 270 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2160 135 135, g32p_row03_traceSegment_013_2160_0135, g32p_row03_traceSegment_013_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2446 8 9, g32p_row03_traceSegment_013_2446_0008, g32p_row03_traceSegment_013_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2430 16 17, g32p_row03_traceSegment_013_2430_0016, g32p_row03_traceSegment_013_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2463 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2463 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2463 8 9, g32p_row03_traceSegment_013_2463_0008, g32p_row03_traceSegment_013_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2488 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2480 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2480 8 9, g32p_row03_traceSegment_013_2480_0008, g32p_row03_traceSegment_013_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2463 34 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2463 17 17, g32p_row03_traceSegment_013_2463_0017, g32p_row03_traceSegment_013_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 2430 67 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2430 33 34, g32p_row03_traceSegment_013_2430_0033, g32p_row03_traceSegment_013_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2497 8 9, g32p_row03_traceSegment_013_2497_0008, g32p_row03_traceSegment_013_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2514 8 9, g32p_row03_traceSegment_013_2514_0008, g32p_row03_traceSegment_013_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2497 17 17, g32p_row03_traceSegment_013_2497_0017, g32p_row03_traceSegment_013_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2539 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2531 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2531 8 9, g32p_row03_traceSegment_013_2531_0008, g32p_row03_traceSegment_013_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2548 8 9, g32p_row03_traceSegment_013_2548_0008, g32p_row03_traceSegment_013_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2531 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2531 17 17, g32p_row03_traceSegment_013_2531_0017, g32p_row03_traceSegment_013_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 2497 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2497 34 34, g32p_row03_traceSegment_013_2497_0034, g32p_row03_traceSegment_013_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 2430 135 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2430 67 68, g32p_row03_traceSegment_013_2430_0067, g32p_row03_traceSegment_013_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 2565 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2581 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2581 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2581 8 9, g32p_row03_traceSegment_013_2581_0008, g32p_row03_traceSegment_013_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 2565 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2565 16 17, g32p_row03_traceSegment_013_2565_0016, g32p_row03_traceSegment_013_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2598 8 9, g32p_row03_traceSegment_013_2598_0008, g32p_row03_traceSegment_013_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2615 8 9, g32p_row03_traceSegment_013_2615_0008, g32p_row03_traceSegment_013_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2598 17 17, g32p_row03_traceSegment_013_2598_0017, g32p_row03_traceSegment_013_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 2565 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2565 33 34, g32p_row03_traceSegment_013_2565_0033, g32p_row03_traceSegment_013_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2640 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2632 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2632 8 9, g32p_row03_traceSegment_013_2632_0008, g32p_row03_traceSegment_013_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2657 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2649 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2649 8 9, g32p_row03_traceSegment_013_2649_0008, g32p_row03_traceSegment_013_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2632 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2632 17 17, g32p_row03_traceSegment_013_2632_0017, g32p_row03_traceSegment_013_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2666 8 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2666 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2666 8 9, g32p_row03_traceSegment_013_2666_0008, g32p_row03_traceSegment_013_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2683 8 9, g32p_row03_traceSegment_013_2683_0008, g32p_row03_traceSegment_013_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2666 34 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2666 17 17, g32p_row03_traceSegment_013_2666_0017, g32p_row03_traceSegment_013_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 2632 68 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2632 34 34, g32p_row03_traceSegment_013_2632_0034, g32p_row03_traceSegment_013_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 2565 135 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2565 67 68, g32p_row03_traceSegment_013_2565_0067, g32p_row03_traceSegment_013_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 2430 270 = [0, 0, 5, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2430 135 135, g32p_row03_traceSegment_013_2430_0135, g32p_row03_traceSegment_013_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_013 2160 540 = [0, 0, 7, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2160 270 270, g32p_row03_traceSegment_013_2160_0270, g32p_row03_traceSegment_013_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2716 8 9, g32p_row03_traceSegment_013_2716_0008, g32p_row03_traceSegment_013_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2700 16 17, g32p_row03_traceSegment_013_2700_0016, g32p_row03_traceSegment_013_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2733 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2733 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2733 8 9, g32p_row03_traceSegment_013_2733_0008, g32p_row03_traceSegment_013_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2750 8 9, g32p_row03_traceSegment_013_2750_0008, g32p_row03_traceSegment_013_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2733 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2733 17 17, g32p_row03_traceSegment_013_2733_0017, g32p_row03_traceSegment_013_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 2700 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2700 33 34, g32p_row03_traceSegment_013_2700_0033, g32p_row03_traceSegment_013_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2767 8 9, g32p_row03_traceSegment_013_2767_0008, g32p_row03_traceSegment_013_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2784 8 9, g32p_row03_traceSegment_013_2784_0008, g32p_row03_traceSegment_013_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2767 17 17, g32p_row03_traceSegment_013_2767_0017, g32p_row03_traceSegment_013_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2801 8 9, g32p_row03_traceSegment_013_2801_0008, g32p_row03_traceSegment_013_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2818 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2818 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2818 8 9, g32p_row03_traceSegment_013_2818_0008, g32p_row03_traceSegment_013_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2801 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2801 17 17, g32p_row03_traceSegment_013_2801_0017, g32p_row03_traceSegment_013_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 2767 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2767 34 34, g32p_row03_traceSegment_013_2767_0034, g32p_row03_traceSegment_013_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 2700 135 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2700 67 68, g32p_row03_traceSegment_013_2700_0067, g32p_row03_traceSegment_013_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2851 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2851 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2851 8 9, g32p_row03_traceSegment_013_2851_0008, g32p_row03_traceSegment_013_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 2835 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2835 16 17, g32p_row03_traceSegment_013_2835_0016, g32p_row03_traceSegment_013_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2868 8 9, g32p_row03_traceSegment_013_2868_0008, g32p_row03_traceSegment_013_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2885 8 9, g32p_row03_traceSegment_013_2885_0008, g32p_row03_traceSegment_013_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2868 17 17, g32p_row03_traceSegment_013_2868_0017, g32p_row03_traceSegment_013_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 2835 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2835 33 34, g32p_row03_traceSegment_013_2835_0033, g32p_row03_traceSegment_013_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2902 8 9, g32p_row03_traceSegment_013_2902_0008, g32p_row03_traceSegment_013_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2919 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2919 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2919 8 9, g32p_row03_traceSegment_013_2919_0008, g32p_row03_traceSegment_013_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2902 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2902 17 17, g32p_row03_traceSegment_013_2902_0017, g32p_row03_traceSegment_013_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2936 8 9, g32p_row03_traceSegment_013_2936_0008, g32p_row03_traceSegment_013_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2961 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2953 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2953 8 9, g32p_row03_traceSegment_013_2953_0008, g32p_row03_traceSegment_013_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 2936 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2936 17 17, g32p_row03_traceSegment_013_2936_0017, g32p_row03_traceSegment_013_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 2902 68 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2902 34 34, g32p_row03_traceSegment_013_2902_0034, g32p_row03_traceSegment_013_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 2835 135 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2835 67 68, g32p_row03_traceSegment_013_2835_0067, g32p_row03_traceSegment_013_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 2700 270 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2700 135 135, g32p_row03_traceSegment_013_2700_0135, g32p_row03_traceSegment_013_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 2994 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 2986 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2986 8 9, g32p_row03_traceSegment_013_2986_0008, g32p_row03_traceSegment_013_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 2970 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2970 16 17, g32p_row03_traceSegment_013_2970_0016, g32p_row03_traceSegment_013_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3003 8 9, g32p_row03_traceSegment_013_3003_0008, g32p_row03_traceSegment_013_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3028 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3020 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3020 8 9, g32p_row03_traceSegment_013_3020_0008, g32p_row03_traceSegment_013_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3003 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3003 17 17, g32p_row03_traceSegment_013_3003_0017, g32p_row03_traceSegment_013_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 2970 67 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2970 33 34, g32p_row03_traceSegment_013_2970_0033, g32p_row03_traceSegment_013_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3037 8 9, g32p_row03_traceSegment_013_3037_0008, g32p_row03_traceSegment_013_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3054 8 9, g32p_row03_traceSegment_013_3054_0008, g32p_row03_traceSegment_013_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3037 17 17, g32p_row03_traceSegment_013_3037_0017, g32p_row03_traceSegment_013_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3071 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3079 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3071 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3071 8 9, g32p_row03_traceSegment_013_3071_0008, g32p_row03_traceSegment_013_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3088 8 9, g32p_row03_traceSegment_013_3088_0008, g32p_row03_traceSegment_013_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3071 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3071 17 17, g32p_row03_traceSegment_013_3071_0017, g32p_row03_traceSegment_013_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 3037 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3037 34 34, g32p_row03_traceSegment_013_3037_0034, g32p_row03_traceSegment_013_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 2970 135 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2970 67 68, g32p_row03_traceSegment_013_2970_0067, g32p_row03_traceSegment_013_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 3105 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3121 8 9, g32p_row03_traceSegment_013_3121_0008, g32p_row03_traceSegment_013_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 3105 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3105 16 17, g32p_row03_traceSegment_013_3105_0016, g32p_row03_traceSegment_013_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3138 8 9, g32p_row03_traceSegment_013_3138_0008, g32p_row03_traceSegment_013_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3155 8 9, g32p_row03_traceSegment_013_3155_0008, g32p_row03_traceSegment_013_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3138 17 17, g32p_row03_traceSegment_013_3138_0017, g32p_row03_traceSegment_013_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 3105 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3105 33 34, g32p_row03_traceSegment_013_3105_0033, g32p_row03_traceSegment_013_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3172 8 9, g32p_row03_traceSegment_013_3172_0008, g32p_row03_traceSegment_013_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3189 8 9, g32p_row03_traceSegment_013_3189_0008, g32p_row03_traceSegment_013_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3172 17 17, g32p_row03_traceSegment_013_3172_0017, g32p_row03_traceSegment_013_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3206 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3206 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3206 8 9, g32p_row03_traceSegment_013_3206_0008, g32p_row03_traceSegment_013_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3231 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3223 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3223 8 9, g32p_row03_traceSegment_013_3223_0008, g32p_row03_traceSegment_013_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3206 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3206 17 17, g32p_row03_traceSegment_013_3206_0017, g32p_row03_traceSegment_013_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 3172 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3172 34 34, g32p_row03_traceSegment_013_3172_0034, g32p_row03_traceSegment_013_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 3105 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3105 67 68, g32p_row03_traceSegment_013_3105_0067, g32p_row03_traceSegment_013_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 2970 270 = [0, 0, 6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2970 135 135, g32p_row03_traceSegment_013_2970_0135, g32p_row03_traceSegment_013_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_013 2700 540 = [0, 0, 9, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2700 270 270, g32p_row03_traceSegment_013_2700_0270, g32p_row03_traceSegment_013_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_013 2160 1080 = [0, 0, 16, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2160 540 540, g32p_row03_traceSegment_013_2160_0540, g32p_row03_traceSegment_013_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3256 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3256 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3256 8 9, g32p_row03_traceSegment_013_3256_0008, g32p_row03_traceSegment_013_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 3240 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3240 16 17, g32p_row03_traceSegment_013_3240_0016, g32p_row03_traceSegment_013_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3273 8 9, g32p_row03_traceSegment_013_3273_0008, g32p_row03_traceSegment_013_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3290 8 9, g32p_row03_traceSegment_013_3290_0008, g32p_row03_traceSegment_013_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3273 17 17, g32p_row03_traceSegment_013_3273_0017, g32p_row03_traceSegment_013_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 3240 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3240 33 34, g32p_row03_traceSegment_013_3240_0033, g32p_row03_traceSegment_013_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3307 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3307 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3307 8 9, g32p_row03_traceSegment_013_3307_0008, g32p_row03_traceSegment_013_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3324 8 9, g32p_row03_traceSegment_013_3324_0008, g32p_row03_traceSegment_013_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3307 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3307 17 17, g32p_row03_traceSegment_013_3307_0017, g32p_row03_traceSegment_013_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3341 8 9, g32p_row03_traceSegment_013_3341_0008, g32p_row03_traceSegment_013_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3366 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3358 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3358 8 9, g32p_row03_traceSegment_013_3358_0008, g32p_row03_traceSegment_013_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3341 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3341 17 17, g32p_row03_traceSegment_013_3341_0017, g32p_row03_traceSegment_013_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 3307 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3307 34 34, g32p_row03_traceSegment_013_3307_0034, g32p_row03_traceSegment_013_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 3240 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3240 67 68, g32p_row03_traceSegment_013_3240_0067, g32p_row03_traceSegment_013_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3391 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3391 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3391 8 9, g32p_row03_traceSegment_013_3391_0008, g32p_row03_traceSegment_013_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 3375 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3375 16 17, g32p_row03_traceSegment_013_3375_0016, g32p_row03_traceSegment_013_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3408 8 9, g32p_row03_traceSegment_013_3408_0008, g32p_row03_traceSegment_013_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3433 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3425 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3425 8 9, g32p_row03_traceSegment_013_3425_0008, g32p_row03_traceSegment_013_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3408 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3408 17 17, g32p_row03_traceSegment_013_3408_0017, g32p_row03_traceSegment_013_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 3375 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3375 33 34, g32p_row03_traceSegment_013_3375_0033, g32p_row03_traceSegment_013_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3442 8 9, g32p_row03_traceSegment_013_3442_0008, g32p_row03_traceSegment_013_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3467 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3459 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3459 8 9, g32p_row03_traceSegment_013_3459_0008, g32p_row03_traceSegment_013_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3442 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3442 17 17, g32p_row03_traceSegment_013_3442_0017, g32p_row03_traceSegment_013_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3476 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3476 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3476 8 9, g32p_row03_traceSegment_013_3476_0008, g32p_row03_traceSegment_013_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3493 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3501 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3493 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3493 8 9, g32p_row03_traceSegment_013_3493_0008, g32p_row03_traceSegment_013_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3476 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3476 17 17, g32p_row03_traceSegment_013_3476_0017, g32p_row03_traceSegment_013_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 3442 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3442 34 34, g32p_row03_traceSegment_013_3442_0034, g32p_row03_traceSegment_013_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 3375 135 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3375 67 68, g32p_row03_traceSegment_013_3375_0067, g32p_row03_traceSegment_013_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 3240 270 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3240 135 135, g32p_row03_traceSegment_013_3240_0135, g32p_row03_traceSegment_013_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 3510 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3534 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3526 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3526 8 9, g32p_row03_traceSegment_013_3526_0008, g32p_row03_traceSegment_013_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 3510 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3510 16 17, g32p_row03_traceSegment_013_3510_0016, g32p_row03_traceSegment_013_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3543 8 9, g32p_row03_traceSegment_013_3543_0008, g32p_row03_traceSegment_013_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3560 8 9, g32p_row03_traceSegment_013_3560_0008, g32p_row03_traceSegment_013_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3543 17 17, g32p_row03_traceSegment_013_3543_0017, g32p_row03_traceSegment_013_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 3510 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3510 33 34, g32p_row03_traceSegment_013_3510_0033, g32p_row03_traceSegment_013_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3577 8 9, g32p_row03_traceSegment_013_3577_0008, g32p_row03_traceSegment_013_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3602 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3594 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3594 8 9, g32p_row03_traceSegment_013_3594_0008, g32p_row03_traceSegment_013_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3577 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3577 17 17, g32p_row03_traceSegment_013_3577_0017, g32p_row03_traceSegment_013_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3611 8 9, g32p_row03_traceSegment_013_3611_0008, g32p_row03_traceSegment_013_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3628 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3636 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3628 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3628 8 9, g32p_row03_traceSegment_013_3628_0008, g32p_row03_traceSegment_013_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3611 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3611 17 17, g32p_row03_traceSegment_013_3611_0017, g32p_row03_traceSegment_013_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 3577 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3577 34 34, g32p_row03_traceSegment_013_3577_0034, g32p_row03_traceSegment_013_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 3510 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3510 67 68, g32p_row03_traceSegment_013_3510_0067, g32p_row03_traceSegment_013_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 3645 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3661 8 9, g32p_row03_traceSegment_013_3661_0008, g32p_row03_traceSegment_013_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 3645 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3645 16 17, g32p_row03_traceSegment_013_3645_0016, g32p_row03_traceSegment_013_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3678 8 9, g32p_row03_traceSegment_013_3678_0008, g32p_row03_traceSegment_013_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3695 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3695 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3695 8 9, g32p_row03_traceSegment_013_3695_0008, g32p_row03_traceSegment_013_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3678 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3678 17 17, g32p_row03_traceSegment_013_3678_0017, g32p_row03_traceSegment_013_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 3645 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3645 33 34, g32p_row03_traceSegment_013_3645_0033, g32p_row03_traceSegment_013_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3712 8 9, g32p_row03_traceSegment_013_3712_0008, g32p_row03_traceSegment_013_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3729 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3729 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3729 8 9, g32p_row03_traceSegment_013_3729_0008, g32p_row03_traceSegment_013_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3712 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3712 17 17, g32p_row03_traceSegment_013_3712_0017, g32p_row03_traceSegment_013_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3746 8 9, g32p_row03_traceSegment_013_3746_0008, g32p_row03_traceSegment_013_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3763 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3763 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3763 8 9, g32p_row03_traceSegment_013_3763_0008, g32p_row03_traceSegment_013_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3746 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3746 17 17, g32p_row03_traceSegment_013_3746_0017, g32p_row03_traceSegment_013_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 3712 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3712 34 34, g32p_row03_traceSegment_013_3712_0034, g32p_row03_traceSegment_013_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 3645 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3645 67 68, g32p_row03_traceSegment_013_3645_0067, g32p_row03_traceSegment_013_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 3510 270 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3510 135 135, g32p_row03_traceSegment_013_3510_0135, g32p_row03_traceSegment_013_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_013 3240 540 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3240 270 270, g32p_row03_traceSegment_013_3240_0270, g32p_row03_traceSegment_013_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 3780 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3796 8 9, g32p_row03_traceSegment_013_3796_0008, g32p_row03_traceSegment_013_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 3780 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3780 16 17, g32p_row03_traceSegment_013_3780_0016, g32p_row03_traceSegment_013_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3813 8 9, g32p_row03_traceSegment_013_3813_0008, g32p_row03_traceSegment_013_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3830 8 9, g32p_row03_traceSegment_013_3830_0008, g32p_row03_traceSegment_013_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3813 17 17, g32p_row03_traceSegment_013_3813_0017, g32p_row03_traceSegment_013_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 3780 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3780 33 34, g32p_row03_traceSegment_013_3780_0033, g32p_row03_traceSegment_013_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3847 8 9, g32p_row03_traceSegment_013_3847_0008, g32p_row03_traceSegment_013_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3864 8 9, g32p_row03_traceSegment_013_3864_0008, g32p_row03_traceSegment_013_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3847 17 17, g32p_row03_traceSegment_013_3847_0017, g32p_row03_traceSegment_013_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3881 8 9, g32p_row03_traceSegment_013_3881_0008, g32p_row03_traceSegment_013_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3898 8 9, g32p_row03_traceSegment_013_3898_0008, g32p_row03_traceSegment_013_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3881 17 17, g32p_row03_traceSegment_013_3881_0017, g32p_row03_traceSegment_013_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3847 34 34, g32p_row03_traceSegment_013_3847_0034, g32p_row03_traceSegment_013_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 3780 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3780 67 68, g32p_row03_traceSegment_013_3780_0067, g32p_row03_traceSegment_013_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3931 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3931 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3931 8 9, g32p_row03_traceSegment_013_3931_0008, g32p_row03_traceSegment_013_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 3915 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3915 16 17, g32p_row03_traceSegment_013_3915_0016, g32p_row03_traceSegment_013_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3948 8 9, g32p_row03_traceSegment_013_3948_0008, g32p_row03_traceSegment_013_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3965 8 9, g32p_row03_traceSegment_013_3965_0008, g32p_row03_traceSegment_013_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3948 17 17, g32p_row03_traceSegment_013_3948_0017, g32p_row03_traceSegment_013_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 3915 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3915 33 34, g32p_row03_traceSegment_013_3915_0033, g32p_row03_traceSegment_013_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3982 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3982 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3982 8 9, g32p_row03_traceSegment_013_3982_0008, g32p_row03_traceSegment_013_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3999 8 9, g32p_row03_traceSegment_013_3999_0008, g32p_row03_traceSegment_013_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 3982 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3982 17 17, g32p_row03_traceSegment_013_3982_0017, g32p_row03_traceSegment_013_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4024 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4016 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4016 8 9, g32p_row03_traceSegment_013_4016_0008, g32p_row03_traceSegment_013_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4041 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4033 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4033 8 9, g32p_row03_traceSegment_013_4033_0008, g32p_row03_traceSegment_013_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 4016 34 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4016 17 17, g32p_row03_traceSegment_013_4016_0017, g32p_row03_traceSegment_013_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 3982 68 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3982 34 34, g32p_row03_traceSegment_013_3982_0034, g32p_row03_traceSegment_013_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 3915 135 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3915 67 68, g32p_row03_traceSegment_013_3915_0067, g32p_row03_traceSegment_013_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 3780 270 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3780 135 135, g32p_row03_traceSegment_013_3780_0135, g32p_row03_traceSegment_013_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4066 8 9, g32p_row03_traceSegment_013_4066_0008, g32p_row03_traceSegment_013_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4050 16 17, g32p_row03_traceSegment_013_4050_0016, g32p_row03_traceSegment_013_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4091 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4083 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4083 8 9, g32p_row03_traceSegment_013_4083_0008, g32p_row03_traceSegment_013_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4100 8 9, g32p_row03_traceSegment_013_4100_0008, g32p_row03_traceSegment_013_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 4083 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4083 17 17, g32p_row03_traceSegment_013_4083_0017, g32p_row03_traceSegment_013_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 4050 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4050 33 34, g32p_row03_traceSegment_013_4050_0033, g32p_row03_traceSegment_013_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4117 8 9, g32p_row03_traceSegment_013_4117_0008, g32p_row03_traceSegment_013_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4134 8 9, g32p_row03_traceSegment_013_4134_0008, g32p_row03_traceSegment_013_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4117 17 17, g32p_row03_traceSegment_013_4117_0017, g32p_row03_traceSegment_013_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4159 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4151 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4151 8 9, g32p_row03_traceSegment_013_4151_0008, g32p_row03_traceSegment_013_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4168 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4176 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4168 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4168 8 9, g32p_row03_traceSegment_013_4168_0008, g32p_row03_traceSegment_013_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 4151 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4151 17 17, g32p_row03_traceSegment_013_4151_0017, g32p_row03_traceSegment_013_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 4117 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4117 34 34, g32p_row03_traceSegment_013_4117_0034, g32p_row03_traceSegment_013_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 4050 135 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4050 67 68, g32p_row03_traceSegment_013_4050_0067, g32p_row03_traceSegment_013_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_013 4185 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4209 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4201 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4201 8 9, g32p_row03_traceSegment_013_4201_0008, g32p_row03_traceSegment_013_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_013 4185 33 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4185 16 17, g32p_row03_traceSegment_013_4185_0016, g32p_row03_traceSegment_013_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4218 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4226 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4218 17 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4218 8 9, g32p_row03_traceSegment_013_4218_0008, g32p_row03_traceSegment_013_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4243 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4235 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4235 8 9, g32p_row03_traceSegment_013_4235_0008, g32p_row03_traceSegment_013_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 4218 34 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4218 17 17, g32p_row03_traceSegment_013_4218_0017, g32p_row03_traceSegment_013_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_013 4185 67 = [0, 0, 6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4185 33 34, g32p_row03_traceSegment_013_4185_0033, g32p_row03_traceSegment_013_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4260 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4252 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4252 8 9, g32p_row03_traceSegment_013_4252_0008, g32p_row03_traceSegment_013_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4269 8 9, g32p_row03_traceSegment_013_4269_0008, g32p_row03_traceSegment_013_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 4252 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4252 17 17, g32p_row03_traceSegment_013_4252_0017, g32p_row03_traceSegment_013_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4286 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4286 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4286 8 9, g32p_row03_traceSegment_013_4286_0008, g32p_row03_traceSegment_013_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_013 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_013 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_013_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_013 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4303 8 9, g32p_row03_traceSegment_013_4303_0008, g32p_row03_traceSegment_013_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_013 4286 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4286 17 17, g32p_row03_traceSegment_013_4286_0017, g32p_row03_traceSegment_013_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_013 4252 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4252 34 34, g32p_row03_traceSegment_013_4252_0034, g32p_row03_traceSegment_013_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_013 4185 135 = [0, 0, 8, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4185 67 68, g32p_row03_traceSegment_013_4185_0067, g32p_row03_traceSegment_013_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_013_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_013 4050 270 = [0, 0, 11, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 4050 135 135, g32p_row03_traceSegment_013_4050_0135, g32p_row03_traceSegment_013_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_013 3780 540 = [0, 0, 13, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3780 270 270, g32p_row03_traceSegment_013_3780_0270, g32p_row03_traceSegment_013_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_013_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_013 3240 1080 = [0, 0, 31, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 3240 540 540, g32p_row03_traceSegment_013_3240_0540, g32p_row03_traceSegment_013_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_013_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_013 2160 2160 = [0, 0, 47, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 2160 1080 1080, g32p_row03_traceSegment_013_2160_1080, g32p_row03_traceSegment_013_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_013_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_013 0 4320 = [0, 0, 90, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_013 0 2160 2160, g32p_row03_traceSegment_013_0000_2160, g32p_row03_traceSegment_013_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 13 = [0, 0, 90, 0, 0, 30] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_013_0000_4320

end HodgeLean.Foundations.Program

end
end
