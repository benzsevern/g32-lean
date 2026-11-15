import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0324
import HodgeLean.Foundations.Program.G32PropFourSixPacked0323
import HodgeLean.Foundations.Program.G32PropFourSixPacked0322

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_047 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 47 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_047_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 16 8 9, g32p_row03_traceSegment_047_0016_0008, g32p_row03_traceSegment_047_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 0 16 17, g32p_row03_traceSegment_047_0000_0016, g32p_row03_traceSegment_047_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 33 8 9, g32p_row03_traceSegment_047_0033_0008, g32p_row03_traceSegment_047_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 50 8 9, g32p_row03_traceSegment_047_0050_0008, g32p_row03_traceSegment_047_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 33 17 17, g32p_row03_traceSegment_047_0033_0017, g32p_row03_traceSegment_047_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 0 33 34, g32p_row03_traceSegment_047_0000_0033, g32p_row03_traceSegment_047_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 67 8 9, g32p_row03_traceSegment_047_0067_0008, g32p_row03_traceSegment_047_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 84 8 9, g32p_row03_traceSegment_047_0084_0008, g32p_row03_traceSegment_047_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 67 17 17, g32p_row03_traceSegment_047_0067_0017, g32p_row03_traceSegment_047_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 101 8 9, g32p_row03_traceSegment_047_0101_0008, g32p_row03_traceSegment_047_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 118 8 9, g32p_row03_traceSegment_047_0118_0008, g32p_row03_traceSegment_047_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 101 17 17, g32p_row03_traceSegment_047_0101_0017, g32p_row03_traceSegment_047_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 67 34 34, g32p_row03_traceSegment_047_0067_0034, g32p_row03_traceSegment_047_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 0 67 68, g32p_row03_traceSegment_047_0000_0067, g32p_row03_traceSegment_047_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 151 8 9, g32p_row03_traceSegment_047_0151_0008, g32p_row03_traceSegment_047_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 135 16 17, g32p_row03_traceSegment_047_0135_0016, g32p_row03_traceSegment_047_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 168 8 9, g32p_row03_traceSegment_047_0168_0008, g32p_row03_traceSegment_047_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 185 8 9, g32p_row03_traceSegment_047_0185_0008, g32p_row03_traceSegment_047_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 168 17 17, g32p_row03_traceSegment_047_0168_0017, g32p_row03_traceSegment_047_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 135 33 34, g32p_row03_traceSegment_047_0135_0033, g32p_row03_traceSegment_047_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 202 8 9, g32p_row03_traceSegment_047_0202_0008, g32p_row03_traceSegment_047_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 219 8 9, g32p_row03_traceSegment_047_0219_0008, g32p_row03_traceSegment_047_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 202 17 17, g32p_row03_traceSegment_047_0202_0017, g32p_row03_traceSegment_047_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 244 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 236 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 236 8 9, g32p_row03_traceSegment_047_0236_0008, g32p_row03_traceSegment_047_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 253 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 261 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 253 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 253 8 9, g32p_row03_traceSegment_047_0253_0008, g32p_row03_traceSegment_047_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 236 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 236 17 17, g32p_row03_traceSegment_047_0236_0017, g32p_row03_traceSegment_047_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 202 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 202 34 34, g32p_row03_traceSegment_047_0202_0034, g32p_row03_traceSegment_047_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 135 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 135 67 68, g32p_row03_traceSegment_047_0135_0067, g32p_row03_traceSegment_047_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 0 270 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 0 135 135, g32p_row03_traceSegment_047_0000_0135, g32p_row03_traceSegment_047_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 270 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 286 8 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 294 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 286 17 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 286 8 9, g32p_row03_traceSegment_047_0286_0008, g32p_row03_traceSegment_047_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 270 33 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 270 16 17, g32p_row03_traceSegment_047_0270_0016, g32p_row03_traceSegment_047_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 303 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 303 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 303 8 9, g32p_row03_traceSegment_047_0303_0008, g32p_row03_traceSegment_047_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 320 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 328 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 320 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 320 8 9, g32p_row03_traceSegment_047_0320_0008, g32p_row03_traceSegment_047_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 303 34 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 303 17 17, g32p_row03_traceSegment_047_0303_0017, g32p_row03_traceSegment_047_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 270 67 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 270 33 34, g32p_row03_traceSegment_047_0270_0033, g32p_row03_traceSegment_047_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 337 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 345 9 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 337 17 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 337 8 9, g32p_row03_traceSegment_047_0337_0008, g32p_row03_traceSegment_047_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 362 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 354 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 354 8 9, g32p_row03_traceSegment_047_0354_0008, g32p_row03_traceSegment_047_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 337 34 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 337 17 17, g32p_row03_traceSegment_047_0337_0017, g32p_row03_traceSegment_047_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 371 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 379 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 371 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 371 8 9, g32p_row03_traceSegment_047_0371_0008, g32p_row03_traceSegment_047_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 388 8 9, g32p_row03_traceSegment_047_0388_0008, g32p_row03_traceSegment_047_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 371 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 371 17 17, g32p_row03_traceSegment_047_0371_0017, g32p_row03_traceSegment_047_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 337 68 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 337 34 34, g32p_row03_traceSegment_047_0337_0034, g32p_row03_traceSegment_047_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 270 135 = [0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 270 67 68, g32p_row03_traceSegment_047_0270_0067, g32p_row03_traceSegment_047_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 421 8 9, g32p_row03_traceSegment_047_0421_0008, g32p_row03_traceSegment_047_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 405 16 17, g32p_row03_traceSegment_047_0405_0016, g32p_row03_traceSegment_047_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 438 8 9, g32p_row03_traceSegment_047_0438_0008, g32p_row03_traceSegment_047_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 455 8 9, g32p_row03_traceSegment_047_0455_0008, g32p_row03_traceSegment_047_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 438 17 17, g32p_row03_traceSegment_047_0438_0017, g32p_row03_traceSegment_047_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 405 33 34, g32p_row03_traceSegment_047_0405_0033, g32p_row03_traceSegment_047_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 472 8 9, g32p_row03_traceSegment_047_0472_0008, g32p_row03_traceSegment_047_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 489 8 9, g32p_row03_traceSegment_047_0489_0008, g32p_row03_traceSegment_047_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 472 17 17, g32p_row03_traceSegment_047_0472_0017, g32p_row03_traceSegment_047_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 506 8 9, g32p_row03_traceSegment_047_0506_0008, g32p_row03_traceSegment_047_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 523 8 9, g32p_row03_traceSegment_047_0523_0008, g32p_row03_traceSegment_047_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 506 17 17, g32p_row03_traceSegment_047_0506_0017, g32p_row03_traceSegment_047_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 472 34 34, g32p_row03_traceSegment_047_0472_0034, g32p_row03_traceSegment_047_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 405 67 68, g32p_row03_traceSegment_047_0405_0067, g32p_row03_traceSegment_047_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 270 270 = [0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 270 135 135, g32p_row03_traceSegment_047_0270_0135, g32p_row03_traceSegment_047_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_047 0 540 = [0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 0 270 270, g32p_row03_traceSegment_047_0000_0270, g32p_row03_traceSegment_047_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 556 8 9, g32p_row03_traceSegment_047_0556_0008, g32p_row03_traceSegment_047_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 540 16 17, g32p_row03_traceSegment_047_0540_0016, g32p_row03_traceSegment_047_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 573 8 9, g32p_row03_traceSegment_047_0573_0008, g32p_row03_traceSegment_047_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 590 8 9, g32p_row03_traceSegment_047_0590_0008, g32p_row03_traceSegment_047_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 573 17 17, g32p_row03_traceSegment_047_0573_0017, g32p_row03_traceSegment_047_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 540 33 34, g32p_row03_traceSegment_047_0540_0033, g32p_row03_traceSegment_047_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 607 8 9, g32p_row03_traceSegment_047_0607_0008, g32p_row03_traceSegment_047_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 624 8 9, g32p_row03_traceSegment_047_0624_0008, g32p_row03_traceSegment_047_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 607 17 17, g32p_row03_traceSegment_047_0607_0017, g32p_row03_traceSegment_047_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 641 8 9, g32p_row03_traceSegment_047_0641_0008, g32p_row03_traceSegment_047_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 658 8 9, g32p_row03_traceSegment_047_0658_0008, g32p_row03_traceSegment_047_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 641 17 17, g32p_row03_traceSegment_047_0641_0017, g32p_row03_traceSegment_047_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 607 34 34, g32p_row03_traceSegment_047_0607_0034, g32p_row03_traceSegment_047_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 540 67 68, g32p_row03_traceSegment_047_0540_0067, g32p_row03_traceSegment_047_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 691 8 9, g32p_row03_traceSegment_047_0691_0008, g32p_row03_traceSegment_047_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 675 16 17, g32p_row03_traceSegment_047_0675_0016, g32p_row03_traceSegment_047_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 708 8 9, g32p_row03_traceSegment_047_0708_0008, g32p_row03_traceSegment_047_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 725 8 9, g32p_row03_traceSegment_047_0725_0008, g32p_row03_traceSegment_047_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 708 17 17, g32p_row03_traceSegment_047_0708_0017, g32p_row03_traceSegment_047_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 675 33 34, g32p_row03_traceSegment_047_0675_0033, g32p_row03_traceSegment_047_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 742 8 9, g32p_row03_traceSegment_047_0742_0008, g32p_row03_traceSegment_047_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 759 8 9, g32p_row03_traceSegment_047_0759_0008, g32p_row03_traceSegment_047_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 742 17 17, g32p_row03_traceSegment_047_0742_0017, g32p_row03_traceSegment_047_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 776 8 9, g32p_row03_traceSegment_047_0776_0008, g32p_row03_traceSegment_047_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 793 8 9, g32p_row03_traceSegment_047_0793_0008, g32p_row03_traceSegment_047_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 776 17 17, g32p_row03_traceSegment_047_0776_0017, g32p_row03_traceSegment_047_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 742 34 34, g32p_row03_traceSegment_047_0742_0034, g32p_row03_traceSegment_047_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 675 67 68, g32p_row03_traceSegment_047_0675_0067, g32p_row03_traceSegment_047_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 540 135 135, g32p_row03_traceSegment_047_0540_0135, g32p_row03_traceSegment_047_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 810 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 834 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 826 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 826 8 9, g32p_row03_traceSegment_047_0826_0008, g32p_row03_traceSegment_047_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 810 33 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 810 16 17, g32p_row03_traceSegment_047_0810_0016, g32p_row03_traceSegment_047_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 851 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 843 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 843 8 9, g32p_row03_traceSegment_047_0843_0008, g32p_row03_traceSegment_047_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 860 8 9, g32p_row03_traceSegment_047_0860_0008, g32p_row03_traceSegment_047_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 843 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 843 17 17, g32p_row03_traceSegment_047_0843_0017, g32p_row03_traceSegment_047_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 810 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 810 33 34, g32p_row03_traceSegment_047_0810_0033, g32p_row03_traceSegment_047_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 885 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 877 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 877 8 9, g32p_row03_traceSegment_047_0877_0008, g32p_row03_traceSegment_047_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 902 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 894 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 894 8 9, g32p_row03_traceSegment_047_0894_0008, g32p_row03_traceSegment_047_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 877 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 877 17 17, g32p_row03_traceSegment_047_0877_0017, g32p_row03_traceSegment_047_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 911 8 9, g32p_row03_traceSegment_047_0911_0008, g32p_row03_traceSegment_047_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 928 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 928 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 928 8 9, g32p_row03_traceSegment_047_0928_0008, g32p_row03_traceSegment_047_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 911 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 911 17 17, g32p_row03_traceSegment_047_0911_0017, g32p_row03_traceSegment_047_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 877 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 877 34 34, g32p_row03_traceSegment_047_0877_0034, g32p_row03_traceSegment_047_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 810 135 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 810 67 68, g32p_row03_traceSegment_047_0810_0067, g32p_row03_traceSegment_047_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 945 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 969 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 961 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 961 8 9, g32p_row03_traceSegment_047_0961_0008, g32p_row03_traceSegment_047_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 945 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 945 16 17, g32p_row03_traceSegment_047_0945_0016, g32p_row03_traceSegment_047_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 978 8 9, g32p_row03_traceSegment_047_0978_0008, g32p_row03_traceSegment_047_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 995 8 9, g32p_row03_traceSegment_047_0995_0008, g32p_row03_traceSegment_047_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 978 17 17, g32p_row03_traceSegment_047_0978_0017, g32p_row03_traceSegment_047_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 945 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 945 33 34, g32p_row03_traceSegment_047_0945_0033, g32p_row03_traceSegment_047_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1020 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1012 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1012 8 9, g32p_row03_traceSegment_047_1012_0008, g32p_row03_traceSegment_047_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1037 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1029 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1029 8 9, g32p_row03_traceSegment_047_1029_0008, g32p_row03_traceSegment_047_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1012 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1012 17 17, g32p_row03_traceSegment_047_1012_0017, g32p_row03_traceSegment_047_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1046 8 9, g32p_row03_traceSegment_047_1046_0008, g32p_row03_traceSegment_047_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1071 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1063 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1063 8 9, g32p_row03_traceSegment_047_1063_0008, g32p_row03_traceSegment_047_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1046 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1046 17 17, g32p_row03_traceSegment_047_1046_0017, g32p_row03_traceSegment_047_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 1012 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1012 34 34, g32p_row03_traceSegment_047_1012_0034, g32p_row03_traceSegment_047_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 945 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 945 67 68, g32p_row03_traceSegment_047_0945_0067, g32p_row03_traceSegment_047_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 810 270 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 810 135 135, g32p_row03_traceSegment_047_0810_0135, g32p_row03_traceSegment_047_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_047 540 540 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 540 270 270, g32p_row03_traceSegment_047_0540_0270, g32p_row03_traceSegment_047_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_047 0 1080 = [0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 0 540 540, g32p_row03_traceSegment_047_0000_0540, g32p_row03_traceSegment_047_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1096 8 9, g32p_row03_traceSegment_047_1096_0008, g32p_row03_traceSegment_047_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1080 16 17, g32p_row03_traceSegment_047_1080_0016, g32p_row03_traceSegment_047_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1113 8 9, g32p_row03_traceSegment_047_1113_0008, g32p_row03_traceSegment_047_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1130 8 9, g32p_row03_traceSegment_047_1130_0008, g32p_row03_traceSegment_047_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1113 17 17, g32p_row03_traceSegment_047_1113_0017, g32p_row03_traceSegment_047_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1080 33 34, g32p_row03_traceSegment_047_1080_0033, g32p_row03_traceSegment_047_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1147 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1147 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1147 8 9, g32p_row03_traceSegment_047_1147_0008, g32p_row03_traceSegment_047_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1164 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1164 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1164 8 9, g32p_row03_traceSegment_047_1164_0008, g32p_row03_traceSegment_047_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1147 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1147 17 17, g32p_row03_traceSegment_047_1147_0017, g32p_row03_traceSegment_047_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1181 8 9, g32p_row03_traceSegment_047_1181_0008, g32p_row03_traceSegment_047_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1198 8 9, g32p_row03_traceSegment_047_1198_0008, g32p_row03_traceSegment_047_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1181 17 17, g32p_row03_traceSegment_047_1181_0017, g32p_row03_traceSegment_047_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 1147 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1147 34 34, g32p_row03_traceSegment_047_1147_0034, g32p_row03_traceSegment_047_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 1080 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1080 67 68, g32p_row03_traceSegment_047_1080_0067, g32p_row03_traceSegment_047_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1231 8 9, g32p_row03_traceSegment_047_1231_0008, g32p_row03_traceSegment_047_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1215 16 17, g32p_row03_traceSegment_047_1215_0016, g32p_row03_traceSegment_047_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1248 8 9, g32p_row03_traceSegment_047_1248_0008, g32p_row03_traceSegment_047_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1265 8 9, g32p_row03_traceSegment_047_1265_0008, g32p_row03_traceSegment_047_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1248 17 17, g32p_row03_traceSegment_047_1248_0017, g32p_row03_traceSegment_047_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1215 33 34, g32p_row03_traceSegment_047_1215_0033, g32p_row03_traceSegment_047_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1282 8 9, g32p_row03_traceSegment_047_1282_0008, g32p_row03_traceSegment_047_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1299 8 9, g32p_row03_traceSegment_047_1299_0008, g32p_row03_traceSegment_047_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1282 17 17, g32p_row03_traceSegment_047_1282_0017, g32p_row03_traceSegment_047_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1316 8 9, g32p_row03_traceSegment_047_1316_0008, g32p_row03_traceSegment_047_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1341 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1333 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1333 8 9, g32p_row03_traceSegment_047_1333_0008, g32p_row03_traceSegment_047_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1316 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1316 17 17, g32p_row03_traceSegment_047_1316_0017, g32p_row03_traceSegment_047_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 1282 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1282 34 34, g32p_row03_traceSegment_047_1282_0034, g32p_row03_traceSegment_047_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 1215 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1215 67 68, g32p_row03_traceSegment_047_1215_0067, g32p_row03_traceSegment_047_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 1080 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1080 135 135, g32p_row03_traceSegment_047_1080_0135, g32p_row03_traceSegment_047_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1366 8 9, g32p_row03_traceSegment_047_1366_0008, g32p_row03_traceSegment_047_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1350 16 17, g32p_row03_traceSegment_047_1350_0016, g32p_row03_traceSegment_047_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1383 8 9, g32p_row03_traceSegment_047_1383_0008, g32p_row03_traceSegment_047_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1400 8 9, g32p_row03_traceSegment_047_1400_0008, g32p_row03_traceSegment_047_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1383 17 17, g32p_row03_traceSegment_047_1383_0017, g32p_row03_traceSegment_047_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1350 33 34, g32p_row03_traceSegment_047_1350_0033, g32p_row03_traceSegment_047_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1425 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1417 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1417 8 9, g32p_row03_traceSegment_047_1417_0008, g32p_row03_traceSegment_047_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1434 8 9, g32p_row03_traceSegment_047_1434_0008, g32p_row03_traceSegment_047_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1417 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1417 17 17, g32p_row03_traceSegment_047_1417_0017, g32p_row03_traceSegment_047_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1459 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1451 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1451 8 9, g32p_row03_traceSegment_047_1451_0008, g32p_row03_traceSegment_047_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1468 8 9, g32p_row03_traceSegment_047_1468_0008, g32p_row03_traceSegment_047_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1451 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1451 17 17, g32p_row03_traceSegment_047_1451_0017, g32p_row03_traceSegment_047_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 1417 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1417 34 34, g32p_row03_traceSegment_047_1417_0034, g32p_row03_traceSegment_047_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 1350 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1350 67 68, g32p_row03_traceSegment_047_1350_0067, g32p_row03_traceSegment_047_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1501 8 9, g32p_row03_traceSegment_047_1501_0008, g32p_row03_traceSegment_047_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1485 16 17, g32p_row03_traceSegment_047_1485_0016, g32p_row03_traceSegment_047_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1518 8 9, g32p_row03_traceSegment_047_1518_0008, g32p_row03_traceSegment_047_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1535 8 9, g32p_row03_traceSegment_047_1535_0008, g32p_row03_traceSegment_047_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1518 17 17, g32p_row03_traceSegment_047_1518_0017, g32p_row03_traceSegment_047_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1485 33 34, g32p_row03_traceSegment_047_1485_0033, g32p_row03_traceSegment_047_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1560 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1552 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1552 8 9, g32p_row03_traceSegment_047_1552_0008, g32p_row03_traceSegment_047_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1569 8 9, g32p_row03_traceSegment_047_1569_0008, g32p_row03_traceSegment_047_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1552 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1552 17 17, g32p_row03_traceSegment_047_1552_0017, g32p_row03_traceSegment_047_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1586 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1586 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1586 8 9, g32p_row03_traceSegment_047_1586_0008, g32p_row03_traceSegment_047_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1603 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1603 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1603 8 9, g32p_row03_traceSegment_047_1603_0008, g32p_row03_traceSegment_047_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1586 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1586 17 17, g32p_row03_traceSegment_047_1586_0017, g32p_row03_traceSegment_047_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 1552 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1552 34 34, g32p_row03_traceSegment_047_1552_0034, g32p_row03_traceSegment_047_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 1485 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1485 67 68, g32p_row03_traceSegment_047_1485_0067, g32p_row03_traceSegment_047_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 1350 270 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1350 135 135, g32p_row03_traceSegment_047_1350_0135, g32p_row03_traceSegment_047_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_047 1080 540 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1080 270 270, g32p_row03_traceSegment_047_1080_0270, g32p_row03_traceSegment_047_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 1620 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1636 8 9, g32p_row03_traceSegment_047_1636_0008, g32p_row03_traceSegment_047_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 1620 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1620 16 17, g32p_row03_traceSegment_047_1620_0016, g32p_row03_traceSegment_047_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1661 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1653 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1653 8 9, g32p_row03_traceSegment_047_1653_0008, g32p_row03_traceSegment_047_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1670 8 9, g32p_row03_traceSegment_047_1670_0008, g32p_row03_traceSegment_047_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1653 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1653 17 17, g32p_row03_traceSegment_047_1653_0017, g32p_row03_traceSegment_047_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 1620 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1620 33 34, g32p_row03_traceSegment_047_1620_0033, g32p_row03_traceSegment_047_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1695 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1687 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1687 8 9, g32p_row03_traceSegment_047_1687_0008, g32p_row03_traceSegment_047_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1704 8 9, g32p_row03_traceSegment_047_1704_0008, g32p_row03_traceSegment_047_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1687 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1687 17 17, g32p_row03_traceSegment_047_1687_0017, g32p_row03_traceSegment_047_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1721 8 9, g32p_row03_traceSegment_047_1721_0008, g32p_row03_traceSegment_047_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1746 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1738 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1738 8 9, g32p_row03_traceSegment_047_1738_0008, g32p_row03_traceSegment_047_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1721 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1721 17 17, g32p_row03_traceSegment_047_1721_0017, g32p_row03_traceSegment_047_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 1687 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1687 34 34, g32p_row03_traceSegment_047_1687_0034, g32p_row03_traceSegment_047_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 1620 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1620 67 68, g32p_row03_traceSegment_047_1620_0067, g32p_row03_traceSegment_047_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1771 8 9, g32p_row03_traceSegment_047_1771_0008, g32p_row03_traceSegment_047_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1755 16 17, g32p_row03_traceSegment_047_1755_0016, g32p_row03_traceSegment_047_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1788 8 9, g32p_row03_traceSegment_047_1788_0008, g32p_row03_traceSegment_047_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1805 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1813 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1805 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1805 8 9, g32p_row03_traceSegment_047_1805_0008, g32p_row03_traceSegment_047_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1788 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1788 17 17, g32p_row03_traceSegment_047_1788_0017, g32p_row03_traceSegment_047_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 1755 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1755 33 34, g32p_row03_traceSegment_047_1755_0033, g32p_row03_traceSegment_047_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1822 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1822 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1822 8 9, g32p_row03_traceSegment_047_1822_0008, g32p_row03_traceSegment_047_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1839 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1847 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1839 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1839 8 9, g32p_row03_traceSegment_047_1839_0008, g32p_row03_traceSegment_047_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1822 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1822 17 17, g32p_row03_traceSegment_047_1822_0017, g32p_row03_traceSegment_047_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1856 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1856 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1856 8 9, g32p_row03_traceSegment_047_1856_0008, g32p_row03_traceSegment_047_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1873 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1873 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1873 8 9, g32p_row03_traceSegment_047_1873_0008, g32p_row03_traceSegment_047_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1856 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1856 17 17, g32p_row03_traceSegment_047_1856_0017, g32p_row03_traceSegment_047_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 1822 68 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1822 34 34, g32p_row03_traceSegment_047_1822_0034, g32p_row03_traceSegment_047_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 1755 135 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1755 67 68, g32p_row03_traceSegment_047_1755_0067, g32p_row03_traceSegment_047_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 1620 270 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1620 135 135, g32p_row03_traceSegment_047_1620_0135, g32p_row03_traceSegment_047_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1906 8 9, g32p_row03_traceSegment_047_1906_0008, g32p_row03_traceSegment_047_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1890 16 17, g32p_row03_traceSegment_047_1890_0016, g32p_row03_traceSegment_047_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1923 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1931 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1923 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1923 8 9, g32p_row03_traceSegment_047_1923_0008, g32p_row03_traceSegment_047_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1940 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1940 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1940 8 9, g32p_row03_traceSegment_047_1940_0008, g32p_row03_traceSegment_047_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1923 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1923 17 17, g32p_row03_traceSegment_047_1923_0017, g32p_row03_traceSegment_047_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 1890 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1890 33 34, g32p_row03_traceSegment_047_1890_0033, g32p_row03_traceSegment_047_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1957 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1965 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1957 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1957 8 9, g32p_row03_traceSegment_047_1957_0008, g32p_row03_traceSegment_047_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1974 8 9, g32p_row03_traceSegment_047_1974_0008, g32p_row03_traceSegment_047_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1957 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1957 17 17, g32p_row03_traceSegment_047_1957_0017, g32p_row03_traceSegment_047_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 1991 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 1999 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 1991 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1991 8 9, g32p_row03_traceSegment_047_1991_0008, g32p_row03_traceSegment_047_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2008 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2008 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2008 8 9, g32p_row03_traceSegment_047_2008_0008, g32p_row03_traceSegment_047_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 1991 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1991 17 17, g32p_row03_traceSegment_047_1991_0017, g32p_row03_traceSegment_047_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 1957 68 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1957 34 34, g32p_row03_traceSegment_047_1957_0034, g32p_row03_traceSegment_047_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 1890 135 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1890 67 68, g32p_row03_traceSegment_047_1890_0067, g32p_row03_traceSegment_047_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 2025 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2041 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2049 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2041 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2041 8 9, g32p_row03_traceSegment_047_2041_0008, g32p_row03_traceSegment_047_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 2025 33 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2025 16 17, g32p_row03_traceSegment_047_2025_0016, g32p_row03_traceSegment_047_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2058 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2058 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2058 8 9, g32p_row03_traceSegment_047_2058_0008, g32p_row03_traceSegment_047_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2075 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2075 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2075 8 9, g32p_row03_traceSegment_047_2075_0008, g32p_row03_traceSegment_047_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2058 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2058 17 17, g32p_row03_traceSegment_047_2058_0017, g32p_row03_traceSegment_047_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 2025 67 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2025 33 34, g32p_row03_traceSegment_047_2025_0033, g32p_row03_traceSegment_047_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2092 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2092 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2092 8 9, g32p_row03_traceSegment_047_2092_0008, g32p_row03_traceSegment_047_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2109 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2109 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2109 8 9, g32p_row03_traceSegment_047_2109_0008, g32p_row03_traceSegment_047_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2092 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2092 17 17, g32p_row03_traceSegment_047_2092_0017, g32p_row03_traceSegment_047_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2134 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2126 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2126 8 9, g32p_row03_traceSegment_047_2126_0008, g32p_row03_traceSegment_047_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2143 8 9, g32p_row03_traceSegment_047_2143_0008, g32p_row03_traceSegment_047_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2126 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2126 17 17, g32p_row03_traceSegment_047_2126_0017, g32p_row03_traceSegment_047_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 2092 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2092 34 34, g32p_row03_traceSegment_047_2092_0034, g32p_row03_traceSegment_047_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 2025 135 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2025 67 68, g32p_row03_traceSegment_047_2025_0067, g32p_row03_traceSegment_047_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 1890 270 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1890 135 135, g32p_row03_traceSegment_047_1890_0135, g32p_row03_traceSegment_047_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_047 1620 540 = [0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1620 270 270, g32p_row03_traceSegment_047_1620_0270, g32p_row03_traceSegment_047_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_047_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_047 1080 1080 = [0, 0, 37] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 1080 540 540, g32p_row03_traceSegment_047_1080_0540, g32p_row03_traceSegment_047_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_047 0 2160 = [0, 0, 73] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 0 1080 1080, g32p_row03_traceSegment_047_0000_1080, g32p_row03_traceSegment_047_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2184 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2176 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2176 8 9, g32p_row03_traceSegment_047_2176_0008, g32p_row03_traceSegment_047_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 2160 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2160 16 17, g32p_row03_traceSegment_047_2160_0016, g32p_row03_traceSegment_047_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2193 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2193 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2193 8 9, g32p_row03_traceSegment_047_2193_0008, g32p_row03_traceSegment_047_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2218 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2210 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2210 8 9, g32p_row03_traceSegment_047_2210_0008, g32p_row03_traceSegment_047_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2193 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2193 17 17, g32p_row03_traceSegment_047_2193_0017, g32p_row03_traceSegment_047_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 2160 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2160 33 34, g32p_row03_traceSegment_047_2160_0033, g32p_row03_traceSegment_047_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2227 8 9, g32p_row03_traceSegment_047_2227_0008, g32p_row03_traceSegment_047_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2244 8 9, g32p_row03_traceSegment_047_2244_0008, g32p_row03_traceSegment_047_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2227 17 17, g32p_row03_traceSegment_047_2227_0017, g32p_row03_traceSegment_047_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2261 8 9, g32p_row03_traceSegment_047_2261_0008, g32p_row03_traceSegment_047_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2278 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2278 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2278 8 9, g32p_row03_traceSegment_047_2278_0008, g32p_row03_traceSegment_047_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2261 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2261 17 17, g32p_row03_traceSegment_047_2261_0017, g32p_row03_traceSegment_047_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 2227 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2227 34 34, g32p_row03_traceSegment_047_2227_0034, g32p_row03_traceSegment_047_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 2160 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2160 67 68, g32p_row03_traceSegment_047_2160_0067, g32p_row03_traceSegment_047_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 2295 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2311 8 9, g32p_row03_traceSegment_047_2311_0008, g32p_row03_traceSegment_047_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 2295 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2295 16 17, g32p_row03_traceSegment_047_2295_0016, g32p_row03_traceSegment_047_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2328 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2328 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2328 8 9, g32p_row03_traceSegment_047_2328_0008, g32p_row03_traceSegment_047_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2353 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2345 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2345 8 9, g32p_row03_traceSegment_047_2345_0008, g32p_row03_traceSegment_047_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2328 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2328 17 17, g32p_row03_traceSegment_047_2328_0017, g32p_row03_traceSegment_047_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 2295 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2295 33 34, g32p_row03_traceSegment_047_2295_0033, g32p_row03_traceSegment_047_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2362 8 9, g32p_row03_traceSegment_047_2362_0008, g32p_row03_traceSegment_047_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2379 8 9, g32p_row03_traceSegment_047_2379_0008, g32p_row03_traceSegment_047_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2362 17 17, g32p_row03_traceSegment_047_2362_0017, g32p_row03_traceSegment_047_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2396 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2396 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2396 8 9, g32p_row03_traceSegment_047_2396_0008, g32p_row03_traceSegment_047_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2413 8 9, g32p_row03_traceSegment_047_2413_0008, g32p_row03_traceSegment_047_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2396 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2396 17 17, g32p_row03_traceSegment_047_2396_0017, g32p_row03_traceSegment_047_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 2362 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2362 34 34, g32p_row03_traceSegment_047_2362_0034, g32p_row03_traceSegment_047_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 2295 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2295 67 68, g32p_row03_traceSegment_047_2295_0067, g32p_row03_traceSegment_047_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 2160 270 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2160 135 135, g32p_row03_traceSegment_047_2160_0135, g32p_row03_traceSegment_047_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2446 8 9, g32p_row03_traceSegment_047_2446_0008, g32p_row03_traceSegment_047_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2430 16 17, g32p_row03_traceSegment_047_2430_0016, g32p_row03_traceSegment_047_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2463 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2463 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2463 8 9, g32p_row03_traceSegment_047_2463_0008, g32p_row03_traceSegment_047_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2480 8 9, g32p_row03_traceSegment_047_2480_0008, g32p_row03_traceSegment_047_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2463 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2463 17 17, g32p_row03_traceSegment_047_2463_0017, g32p_row03_traceSegment_047_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 2430 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2430 33 34, g32p_row03_traceSegment_047_2430_0033, g32p_row03_traceSegment_047_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2497 8 9, g32p_row03_traceSegment_047_2497_0008, g32p_row03_traceSegment_047_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2514 8 9, g32p_row03_traceSegment_047_2514_0008, g32p_row03_traceSegment_047_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2497 17 17, g32p_row03_traceSegment_047_2497_0017, g32p_row03_traceSegment_047_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2531 8 9, g32p_row03_traceSegment_047_2531_0008, g32p_row03_traceSegment_047_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2548 8 9, g32p_row03_traceSegment_047_2548_0008, g32p_row03_traceSegment_047_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2531 17 17, g32p_row03_traceSegment_047_2531_0017, g32p_row03_traceSegment_047_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2497 34 34, g32p_row03_traceSegment_047_2497_0034, g32p_row03_traceSegment_047_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 2430 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2430 67 68, g32p_row03_traceSegment_047_2430_0067, g32p_row03_traceSegment_047_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 2565 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2581 8 9, g32p_row03_traceSegment_047_2581_0008, g32p_row03_traceSegment_047_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 2565 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2565 16 17, g32p_row03_traceSegment_047_2565_0016, g32p_row03_traceSegment_047_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2606 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2598 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2598 8 9, g32p_row03_traceSegment_047_2598_0008, g32p_row03_traceSegment_047_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2615 8 9, g32p_row03_traceSegment_047_2615_0008, g32p_row03_traceSegment_047_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2598 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2598 17 17, g32p_row03_traceSegment_047_2598_0017, g32p_row03_traceSegment_047_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 2565 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2565 33 34, g32p_row03_traceSegment_047_2565_0033, g32p_row03_traceSegment_047_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2632 8 9, g32p_row03_traceSegment_047_2632_0008, g32p_row03_traceSegment_047_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2649 8 9, g32p_row03_traceSegment_047_2649_0008, g32p_row03_traceSegment_047_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2632 17 17, g32p_row03_traceSegment_047_2632_0017, g32p_row03_traceSegment_047_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2666 8 9, g32p_row03_traceSegment_047_2666_0008, g32p_row03_traceSegment_047_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2683 8 9, g32p_row03_traceSegment_047_2683_0008, g32p_row03_traceSegment_047_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2666 17 17, g32p_row03_traceSegment_047_2666_0017, g32p_row03_traceSegment_047_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2632 34 34, g32p_row03_traceSegment_047_2632_0034, g32p_row03_traceSegment_047_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 2565 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2565 67 68, g32p_row03_traceSegment_047_2565_0067, g32p_row03_traceSegment_047_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 2430 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2430 135 135, g32p_row03_traceSegment_047_2430_0135, g32p_row03_traceSegment_047_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_047 2160 540 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2160 270 270, g32p_row03_traceSegment_047_2160_0270, g32p_row03_traceSegment_047_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2716 8 9, g32p_row03_traceSegment_047_2716_0008, g32p_row03_traceSegment_047_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2700 16 17, g32p_row03_traceSegment_047_2700_0016, g32p_row03_traceSegment_047_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2733 8 9, g32p_row03_traceSegment_047_2733_0008, g32p_row03_traceSegment_047_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2750 8 9, g32p_row03_traceSegment_047_2750_0008, g32p_row03_traceSegment_047_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2733 17 17, g32p_row03_traceSegment_047_2733_0017, g32p_row03_traceSegment_047_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2700 33 34, g32p_row03_traceSegment_047_2700_0033, g32p_row03_traceSegment_047_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2767 8 9, g32p_row03_traceSegment_047_2767_0008, g32p_row03_traceSegment_047_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2784 8 9, g32p_row03_traceSegment_047_2784_0008, g32p_row03_traceSegment_047_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2767 17 17, g32p_row03_traceSegment_047_2767_0017, g32p_row03_traceSegment_047_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2801 8 9, g32p_row03_traceSegment_047_2801_0008, g32p_row03_traceSegment_047_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2818 8 9, g32p_row03_traceSegment_047_2818_0008, g32p_row03_traceSegment_047_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2801 17 17, g32p_row03_traceSegment_047_2801_0017, g32p_row03_traceSegment_047_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2767 34 34, g32p_row03_traceSegment_047_2767_0034, g32p_row03_traceSegment_047_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2700 67 68, g32p_row03_traceSegment_047_2700_0067, g32p_row03_traceSegment_047_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2851 8 9, g32p_row03_traceSegment_047_2851_0008, g32p_row03_traceSegment_047_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2835 16 17, g32p_row03_traceSegment_047_2835_0016, g32p_row03_traceSegment_047_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2868 8 9, g32p_row03_traceSegment_047_2868_0008, g32p_row03_traceSegment_047_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2885 8 9, g32p_row03_traceSegment_047_2885_0008, g32p_row03_traceSegment_047_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2868 17 17, g32p_row03_traceSegment_047_2868_0017, g32p_row03_traceSegment_047_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2835 33 34, g32p_row03_traceSegment_047_2835_0033, g32p_row03_traceSegment_047_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2902 8 9, g32p_row03_traceSegment_047_2902_0008, g32p_row03_traceSegment_047_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2919 8 9, g32p_row03_traceSegment_047_2919_0008, g32p_row03_traceSegment_047_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2902 17 17, g32p_row03_traceSegment_047_2902_0017, g32p_row03_traceSegment_047_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2936 8 9, g32p_row03_traceSegment_047_2936_0008, g32p_row03_traceSegment_047_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2953 8 9, g32p_row03_traceSegment_047_2953_0008, g32p_row03_traceSegment_047_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2936 17 17, g32p_row03_traceSegment_047_2936_0017, g32p_row03_traceSegment_047_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2902 34 34, g32p_row03_traceSegment_047_2902_0034, g32p_row03_traceSegment_047_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2835 67 68, g32p_row03_traceSegment_047_2835_0067, g32p_row03_traceSegment_047_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2700 135 135, g32p_row03_traceSegment_047_2700_0135, g32p_row03_traceSegment_047_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2986 8 9, g32p_row03_traceSegment_047_2986_0008, g32p_row03_traceSegment_047_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2970 16 17, g32p_row03_traceSegment_047_2970_0016, g32p_row03_traceSegment_047_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3003 8 9, g32p_row03_traceSegment_047_3003_0008, g32p_row03_traceSegment_047_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3020 8 9, g32p_row03_traceSegment_047_3020_0008, g32p_row03_traceSegment_047_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3003 17 17, g32p_row03_traceSegment_047_3003_0017, g32p_row03_traceSegment_047_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2970 33 34, g32p_row03_traceSegment_047_2970_0033, g32p_row03_traceSegment_047_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3037 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3037 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3037 8 9, g32p_row03_traceSegment_047_3037_0008, g32p_row03_traceSegment_047_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3062 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3054 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3054 8 9, g32p_row03_traceSegment_047_3054_0008, g32p_row03_traceSegment_047_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3037 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3037 17 17, g32p_row03_traceSegment_047_3037_0017, g32p_row03_traceSegment_047_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3079 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3071 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3071 8 9, g32p_row03_traceSegment_047_3071_0008, g32p_row03_traceSegment_047_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3088 8 9, g32p_row03_traceSegment_047_3088_0008, g32p_row03_traceSegment_047_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3071 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3071 17 17, g32p_row03_traceSegment_047_3071_0017, g32p_row03_traceSegment_047_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 3037 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3037 34 34, g32p_row03_traceSegment_047_3037_0034, g32p_row03_traceSegment_047_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 2970 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2970 67 68, g32p_row03_traceSegment_047_2970_0067, g32p_row03_traceSegment_047_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 3105 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3129 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3121 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3121 8 9, g32p_row03_traceSegment_047_3121_0008, g32p_row03_traceSegment_047_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 3105 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3105 16 17, g32p_row03_traceSegment_047_3105_0016, g32p_row03_traceSegment_047_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3138 8 9, g32p_row03_traceSegment_047_3138_0008, g32p_row03_traceSegment_047_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3155 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3155 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3155 8 9, g32p_row03_traceSegment_047_3155_0008, g32p_row03_traceSegment_047_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3138 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3138 17 17, g32p_row03_traceSegment_047_3138_0017, g32p_row03_traceSegment_047_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 3105 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3105 33 34, g32p_row03_traceSegment_047_3105_0033, g32p_row03_traceSegment_047_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3180 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3172 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3172 8 9, g32p_row03_traceSegment_047_3172_0008, g32p_row03_traceSegment_047_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3189 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3189 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3189 8 9, g32p_row03_traceSegment_047_3189_0008, g32p_row03_traceSegment_047_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3172 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3172 17 17, g32p_row03_traceSegment_047_3172_0017, g32p_row03_traceSegment_047_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3214 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3206 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3206 8 9, g32p_row03_traceSegment_047_3206_0008, g32p_row03_traceSegment_047_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3223 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3223 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3223 8 9, g32p_row03_traceSegment_047_3223_0008, g32p_row03_traceSegment_047_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3206 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3206 17 17, g32p_row03_traceSegment_047_3206_0017, g32p_row03_traceSegment_047_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 3172 68 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3172 34 34, g32p_row03_traceSegment_047_3172_0034, g32p_row03_traceSegment_047_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 3105 135 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3105 67 68, g32p_row03_traceSegment_047_3105_0067, g32p_row03_traceSegment_047_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 2970 270 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2970 135 135, g32p_row03_traceSegment_047_2970_0135, g32p_row03_traceSegment_047_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_047 2700 540 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2700 270 270, g32p_row03_traceSegment_047_2700_0270, g32p_row03_traceSegment_047_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_047 2160 1080 = [0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2160 540 540, g32p_row03_traceSegment_047_2160_0540, g32p_row03_traceSegment_047_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 3240 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3256 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3256 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3256 8 9, g32p_row03_traceSegment_047_3256_0008, g32p_row03_traceSegment_047_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 3240 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3240 16 17, g32p_row03_traceSegment_047_3240_0016, g32p_row03_traceSegment_047_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3273 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3273 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3273 8 9, g32p_row03_traceSegment_047_3273_0008, g32p_row03_traceSegment_047_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3290 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3298 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3290 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3290 8 9, g32p_row03_traceSegment_047_3290_0008, g32p_row03_traceSegment_047_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3273 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3273 17 17, g32p_row03_traceSegment_047_3273_0017, g32p_row03_traceSegment_047_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 3240 67 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3240 33 34, g32p_row03_traceSegment_047_3240_0033, g32p_row03_traceSegment_047_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3307 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3315 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3307 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3307 8 9, g32p_row03_traceSegment_047_3307_0008, g32p_row03_traceSegment_047_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3324 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3332 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3324 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3324 8 9, g32p_row03_traceSegment_047_3324_0008, g32p_row03_traceSegment_047_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3307 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3307 17 17, g32p_row03_traceSegment_047_3307_0017, g32p_row03_traceSegment_047_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3341 8 9, g32p_row03_traceSegment_047_3341_0008, g32p_row03_traceSegment_047_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3358 8 9, g32p_row03_traceSegment_047_3358_0008, g32p_row03_traceSegment_047_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3341 17 17, g32p_row03_traceSegment_047_3341_0017, g32p_row03_traceSegment_047_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 3307 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3307 34 34, g32p_row03_traceSegment_047_3307_0034, g32p_row03_traceSegment_047_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 3240 135 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3240 67 68, g32p_row03_traceSegment_047_3240_0067, g32p_row03_traceSegment_047_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 3375 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3391 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3391 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3391 8 9, g32p_row03_traceSegment_047_3391_0008, g32p_row03_traceSegment_047_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 3375 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3375 16 17, g32p_row03_traceSegment_047_3375_0016, g32p_row03_traceSegment_047_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3408 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3416 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3408 17 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3408 8 9, g32p_row03_traceSegment_047_3408_0008, g32p_row03_traceSegment_047_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3425 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3433 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3425 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3425 8 9, g32p_row03_traceSegment_047_3425_0008, g32p_row03_traceSegment_047_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3408 34 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3408 17 17, g32p_row03_traceSegment_047_3408_0017, g32p_row03_traceSegment_047_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 3375 67 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3375 33 34, g32p_row03_traceSegment_047_3375_0033, g32p_row03_traceSegment_047_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3442 8 9, g32p_row03_traceSegment_047_3442_0008, g32p_row03_traceSegment_047_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3459 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3467 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3459 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3459 8 9, g32p_row03_traceSegment_047_3459_0008, g32p_row03_traceSegment_047_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3442 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3442 17 17, g32p_row03_traceSegment_047_3442_0017, g32p_row03_traceSegment_047_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3484 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3476 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3476 8 9, g32p_row03_traceSegment_047_3476_0008, g32p_row03_traceSegment_047_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3493 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3493 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3493 8 9, g32p_row03_traceSegment_047_3493_0008, g32p_row03_traceSegment_047_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3476 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3476 17 17, g32p_row03_traceSegment_047_3476_0017, g32p_row03_traceSegment_047_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 3442 68 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3442 34 34, g32p_row03_traceSegment_047_3442_0034, g32p_row03_traceSegment_047_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 3375 135 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3375 67 68, g32p_row03_traceSegment_047_3375_0067, g32p_row03_traceSegment_047_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 3240 270 = [0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3240 135 135, g32p_row03_traceSegment_047_3240_0135, g32p_row03_traceSegment_047_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 3510 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3526 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3534 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3526 17 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3526 8 9, g32p_row03_traceSegment_047_3526_0008, g32p_row03_traceSegment_047_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 3510 33 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3510 16 17, g32p_row03_traceSegment_047_3510_0016, g32p_row03_traceSegment_047_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3543 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3543 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3543 8 9, g32p_row03_traceSegment_047_3543_0008, g32p_row03_traceSegment_047_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3560 8 9, g32p_row03_traceSegment_047_3560_0008, g32p_row03_traceSegment_047_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3543 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3543 17 17, g32p_row03_traceSegment_047_3543_0017, g32p_row03_traceSegment_047_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 3510 67 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3510 33 34, g32p_row03_traceSegment_047_3510_0033, g32p_row03_traceSegment_047_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3577 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3585 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3577 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3577 8 9, g32p_row03_traceSegment_047_3577_0008, g32p_row03_traceSegment_047_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3594 8 9, g32p_row03_traceSegment_047_3594_0008, g32p_row03_traceSegment_047_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3577 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3577 17 17, g32p_row03_traceSegment_047_3577_0017, g32p_row03_traceSegment_047_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3611 8 9, g32p_row03_traceSegment_047_3611_0008, g32p_row03_traceSegment_047_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3628 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3628 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3628 8 9, g32p_row03_traceSegment_047_3628_0008, g32p_row03_traceSegment_047_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3611 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3611 17 17, g32p_row03_traceSegment_047_3611_0017, g32p_row03_traceSegment_047_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 3577 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3577 34 34, g32p_row03_traceSegment_047_3577_0034, g32p_row03_traceSegment_047_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 3510 135 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3510 67 68, g32p_row03_traceSegment_047_3510_0067, g32p_row03_traceSegment_047_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 3645 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3669 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3661 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3661 8 9, g32p_row03_traceSegment_047_3661_0008, g32p_row03_traceSegment_047_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 3645 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3645 16 17, g32p_row03_traceSegment_047_3645_0016, g32p_row03_traceSegment_047_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3678 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3686 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3678 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3678 8 9, g32p_row03_traceSegment_047_3678_0008, g32p_row03_traceSegment_047_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3695 8 9, g32p_row03_traceSegment_047_3695_0008, g32p_row03_traceSegment_047_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3678 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3678 17 17, g32p_row03_traceSegment_047_3678_0017, g32p_row03_traceSegment_047_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 3645 67 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3645 33 34, g32p_row03_traceSegment_047_3645_0033, g32p_row03_traceSegment_047_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3720 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3712 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3712 8 9, g32p_row03_traceSegment_047_3712_0008, g32p_row03_traceSegment_047_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3729 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3729 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3729 8 9, g32p_row03_traceSegment_047_3729_0008, g32p_row03_traceSegment_047_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3712 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3712 17 17, g32p_row03_traceSegment_047_3712_0017, g32p_row03_traceSegment_047_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3754 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3746 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3746 8 9, g32p_row03_traceSegment_047_3746_0008, g32p_row03_traceSegment_047_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3763 8 9, g32p_row03_traceSegment_047_3763_0008, g32p_row03_traceSegment_047_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3746 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3746 17 17, g32p_row03_traceSegment_047_3746_0017, g32p_row03_traceSegment_047_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 3712 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3712 34 34, g32p_row03_traceSegment_047_3712_0034, g32p_row03_traceSegment_047_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 3645 135 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3645 67 68, g32p_row03_traceSegment_047_3645_0067, g32p_row03_traceSegment_047_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 3510 270 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3510 135 135, g32p_row03_traceSegment_047_3510_0135, g32p_row03_traceSegment_047_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_047 3240 540 = [0, 0, 41] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3240 270 270, g32p_row03_traceSegment_047_3240_0270, g32p_row03_traceSegment_047_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 3780 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3796 8 9, g32p_row03_traceSegment_047_3796_0008, g32p_row03_traceSegment_047_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 3780 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3780 16 17, g32p_row03_traceSegment_047_3780_0016, g32p_row03_traceSegment_047_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3813 8 9, g32p_row03_traceSegment_047_3813_0008, g32p_row03_traceSegment_047_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3830 8 9, g32p_row03_traceSegment_047_3830_0008, g32p_row03_traceSegment_047_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3813 17 17, g32p_row03_traceSegment_047_3813_0017, g32p_row03_traceSegment_047_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 3780 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3780 33 34, g32p_row03_traceSegment_047_3780_0033, g32p_row03_traceSegment_047_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3847 8 9, g32p_row03_traceSegment_047_3847_0008, g32p_row03_traceSegment_047_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3864 8 9, g32p_row03_traceSegment_047_3864_0008, g32p_row03_traceSegment_047_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3847 17 17, g32p_row03_traceSegment_047_3847_0017, g32p_row03_traceSegment_047_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3881 8 9, g32p_row03_traceSegment_047_3881_0008, g32p_row03_traceSegment_047_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3898 8 9, g32p_row03_traceSegment_047_3898_0008, g32p_row03_traceSegment_047_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3881 17 17, g32p_row03_traceSegment_047_3881_0017, g32p_row03_traceSegment_047_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3847 34 34, g32p_row03_traceSegment_047_3847_0034, g32p_row03_traceSegment_047_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 3780 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3780 67 68, g32p_row03_traceSegment_047_3780_0067, g32p_row03_traceSegment_047_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3931 8 9, g32p_row03_traceSegment_047_3931_0008, g32p_row03_traceSegment_047_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3915 16 17, g32p_row03_traceSegment_047_3915_0016, g32p_row03_traceSegment_047_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3948 8 9, g32p_row03_traceSegment_047_3948_0008, g32p_row03_traceSegment_047_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3965 8 9, g32p_row03_traceSegment_047_3965_0008, g32p_row03_traceSegment_047_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3948 17 17, g32p_row03_traceSegment_047_3948_0017, g32p_row03_traceSegment_047_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3915 33 34, g32p_row03_traceSegment_047_3915_0033, g32p_row03_traceSegment_047_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3982 8 9, g32p_row03_traceSegment_047_3982_0008, g32p_row03_traceSegment_047_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3999 8 9, g32p_row03_traceSegment_047_3999_0008, g32p_row03_traceSegment_047_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3982 17 17, g32p_row03_traceSegment_047_3982_0017, g32p_row03_traceSegment_047_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4016 8 9, g32p_row03_traceSegment_047_4016_0008, g32p_row03_traceSegment_047_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4033 8 9, g32p_row03_traceSegment_047_4033_0008, g32p_row03_traceSegment_047_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4016 17 17, g32p_row03_traceSegment_047_4016_0017, g32p_row03_traceSegment_047_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3982 34 34, g32p_row03_traceSegment_047_3982_0034, g32p_row03_traceSegment_047_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3915 67 68, g32p_row03_traceSegment_047_3915_0067, g32p_row03_traceSegment_047_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 3780 270 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3780 135 135, g32p_row03_traceSegment_047_3780_0135, g32p_row03_traceSegment_047_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4066 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4066 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4066 8 9, g32p_row03_traceSegment_047_4066_0008, g32p_row03_traceSegment_047_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 4050 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4050 16 17, g32p_row03_traceSegment_047_4050_0016, g32p_row03_traceSegment_047_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4083 8 9, g32p_row03_traceSegment_047_4083_0008, g32p_row03_traceSegment_047_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4100 8 9, g32p_row03_traceSegment_047_4100_0008, g32p_row03_traceSegment_047_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4083 17 17, g32p_row03_traceSegment_047_4083_0017, g32p_row03_traceSegment_047_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 4050 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4050 33 34, g32p_row03_traceSegment_047_4050_0033, g32p_row03_traceSegment_047_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4117 8 9, g32p_row03_traceSegment_047_4117_0008, g32p_row03_traceSegment_047_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4134 8 9, g32p_row03_traceSegment_047_4134_0008, g32p_row03_traceSegment_047_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4117 17 17, g32p_row03_traceSegment_047_4117_0017, g32p_row03_traceSegment_047_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4151 8 9, g32p_row03_traceSegment_047_4151_0008, g32p_row03_traceSegment_047_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4168 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4168 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4168 8 9, g32p_row03_traceSegment_047_4168_0008, g32p_row03_traceSegment_047_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 4151 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4151 17 17, g32p_row03_traceSegment_047_4151_0017, g32p_row03_traceSegment_047_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 4117 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4117 34 34, g32p_row03_traceSegment_047_4117_0034, g32p_row03_traceSegment_047_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 4050 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4050 67 68, g32p_row03_traceSegment_047_4050_0067, g32p_row03_traceSegment_047_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_047 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4209 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4201 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4201 8 9, g32p_row03_traceSegment_047_4201_0008, g32p_row03_traceSegment_047_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_047 4185 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4185 16 17, g32p_row03_traceSegment_047_4185_0016, g32p_row03_traceSegment_047_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4226 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4218 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4218 8 9, g32p_row03_traceSegment_047_4218_0008, g32p_row03_traceSegment_047_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4235 8 9, g32p_row03_traceSegment_047_4235_0008, g32p_row03_traceSegment_047_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 4218 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4218 17 17, g32p_row03_traceSegment_047_4218_0017, g32p_row03_traceSegment_047_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_047 4185 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4185 33 34, g32p_row03_traceSegment_047_4185_0033, g32p_row03_traceSegment_047_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4252 8 9, g32p_row03_traceSegment_047_4252_0008, g32p_row03_traceSegment_047_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4269 8 9, g32p_row03_traceSegment_047_4269_0008, g32p_row03_traceSegment_047_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4252 17 17, g32p_row03_traceSegment_047_4252_0017, g32p_row03_traceSegment_047_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4286 8 9, g32p_row03_traceSegment_047_4286_0008, g32p_row03_traceSegment_047_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_047 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_047 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_047_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_047 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4303 8 9, g32p_row03_traceSegment_047_4303_0008, g32p_row03_traceSegment_047_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_047 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4286 17 17, g32p_row03_traceSegment_047_4286_0017, g32p_row03_traceSegment_047_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_047 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4252 34 34, g32p_row03_traceSegment_047_4252_0034, g32p_row03_traceSegment_047_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_047 4185 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4185 67 68, g32p_row03_traceSegment_047_4185_0067, g32p_row03_traceSegment_047_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_047_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_047 4050 270 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 4050 135 135, g32p_row03_traceSegment_047_4050_0135, g32p_row03_traceSegment_047_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_047 3780 540 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3780 270 270, g32p_row03_traceSegment_047_3780_0270, g32p_row03_traceSegment_047_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_047_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_047 3240 1080 = [0, 0, 47] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 3240 540 540, g32p_row03_traceSegment_047_3240_0540, g32p_row03_traceSegment_047_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_047_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_047 2160 2160 = [0, 0, 71] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 2160 1080 1080, g32p_row03_traceSegment_047_2160_1080, g32p_row03_traceSegment_047_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_047_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_047 0 4320 = [0, 0, 144] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_047 0 2160 2160, g32p_row03_traceSegment_047_0000_2160, g32p_row03_traceSegment_047_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_047 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 47 = [0, 0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_047_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_049 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 49 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_049_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 0 16 = [0, 0, 4, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 24 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 16 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 16 8 9, g32p_row03_traceSegment_049_0016_0008, g32p_row03_traceSegment_049_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 0 33 = [0, 0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 0 16 17, g32p_row03_traceSegment_049_0000_0016, g32p_row03_traceSegment_049_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 33 8 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 41 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 33 17 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 33 8 9, g32p_row03_traceSegment_049_0033_0008, g32p_row03_traceSegment_049_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 50 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 58 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 50 17 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 50 8 9, g32p_row03_traceSegment_049_0050_0008, g32p_row03_traceSegment_049_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 33 34 = [0, 0, 3, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 33 17 17, g32p_row03_traceSegment_049_0033_0017, g32p_row03_traceSegment_049_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 0 67 = [0, 0, 8, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 0 33 34, g32p_row03_traceSegment_049_0000_0033, g32p_row03_traceSegment_049_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 67 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 67 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 67 8 9, g32p_row03_traceSegment_049_0067_0008, g32p_row03_traceSegment_049_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 84 8 9, g32p_row03_traceSegment_049_0084_0008, g32p_row03_traceSegment_049_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 67 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 67 17 17, g32p_row03_traceSegment_049_0067_0017, g32p_row03_traceSegment_049_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 101 8 9, g32p_row03_traceSegment_049_0101_0008, g32p_row03_traceSegment_049_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 118 8 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 126 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 118 17 = [0, 0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 118 8 9, g32p_row03_traceSegment_049_0118_0008, g32p_row03_traceSegment_049_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 101 34 = [0, 0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 101 17 17, g32p_row03_traceSegment_049_0101_0017, g32p_row03_traceSegment_049_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 67 68 = [0, 0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 67 34 34, g32p_row03_traceSegment_049_0067_0034, g32p_row03_traceSegment_049_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 0 135 = [0, 0, 12, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 0 67 68, g32p_row03_traceSegment_049_0000_0067, g32p_row03_traceSegment_049_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 151 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 159 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 151 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 151 8 9, g32p_row03_traceSegment_049_0151_0008, g32p_row03_traceSegment_049_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 135 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 135 16 17, g32p_row03_traceSegment_049_0135_0016, g32p_row03_traceSegment_049_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 168 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 168 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 168 8 9, g32p_row03_traceSegment_049_0168_0008, g32p_row03_traceSegment_049_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 185 8 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 193 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 185 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 185 8 9, g32p_row03_traceSegment_049_0185_0008, g32p_row03_traceSegment_049_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 168 34 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 168 17 17, g32p_row03_traceSegment_049_0168_0017, g32p_row03_traceSegment_049_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 135 67 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 135 33 34, g32p_row03_traceSegment_049_0135_0033, g32p_row03_traceSegment_049_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 202 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 210 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 202 17 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 202 8 9, g32p_row03_traceSegment_049_0202_0008, g32p_row03_traceSegment_049_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 219 8 9, g32p_row03_traceSegment_049_0219_0008, g32p_row03_traceSegment_049_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 202 34 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 202 17 17, g32p_row03_traceSegment_049_0202_0017, g32p_row03_traceSegment_049_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 236 8 9, g32p_row03_traceSegment_049_0236_0008, g32p_row03_traceSegment_049_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 253 8 9, g32p_row03_traceSegment_049_0253_0008, g32p_row03_traceSegment_049_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 236 17 17, g32p_row03_traceSegment_049_0236_0017, g32p_row03_traceSegment_049_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 202 68 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 202 34 34, g32p_row03_traceSegment_049_0202_0034, g32p_row03_traceSegment_049_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 135 135 = [0, 0, 1, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 135 67 68, g32p_row03_traceSegment_049_0135_0067, g32p_row03_traceSegment_049_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 0 270 = [0, 0, 13, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 0 135 135, g32p_row03_traceSegment_049_0000_0135, g32p_row03_traceSegment_049_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 286 8 9, g32p_row03_traceSegment_049_0286_0008, g32p_row03_traceSegment_049_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 270 16 17, g32p_row03_traceSegment_049_0270_0016, g32p_row03_traceSegment_049_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 303 8 9, g32p_row03_traceSegment_049_0303_0008, g32p_row03_traceSegment_049_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 320 8 9, g32p_row03_traceSegment_049_0320_0008, g32p_row03_traceSegment_049_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 303 17 17, g32p_row03_traceSegment_049_0303_0017, g32p_row03_traceSegment_049_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 270 33 34, g32p_row03_traceSegment_049_0270_0033, g32p_row03_traceSegment_049_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 337 8 9, g32p_row03_traceSegment_049_0337_0008, g32p_row03_traceSegment_049_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 354 8 9, g32p_row03_traceSegment_049_0354_0008, g32p_row03_traceSegment_049_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 337 17 17, g32p_row03_traceSegment_049_0337_0017, g32p_row03_traceSegment_049_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 371 8 9, g32p_row03_traceSegment_049_0371_0008, g32p_row03_traceSegment_049_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 396 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 388 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 388 8 9, g32p_row03_traceSegment_049_0388_0008, g32p_row03_traceSegment_049_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 371 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 371 17 17, g32p_row03_traceSegment_049_0371_0017, g32p_row03_traceSegment_049_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 337 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 337 34 34, g32p_row03_traceSegment_049_0337_0034, g32p_row03_traceSegment_049_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 270 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 270 67 68, g32p_row03_traceSegment_049_0270_0067, g32p_row03_traceSegment_049_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 405 16 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 421 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 429 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 421 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 421 8 9, g32p_row03_traceSegment_049_0421_0008, g32p_row03_traceSegment_049_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 405 33 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 405 16 17, g32p_row03_traceSegment_049_0405_0016, g32p_row03_traceSegment_049_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 438 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 446 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 438 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 438 8 9, g32p_row03_traceSegment_049_0438_0008, g32p_row03_traceSegment_049_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 455 8 9, g32p_row03_traceSegment_049_0455_0008, g32p_row03_traceSegment_049_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 438 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 438 17 17, g32p_row03_traceSegment_049_0438_0017, g32p_row03_traceSegment_049_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 405 67 = [0, 0, 2, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 405 33 34, g32p_row03_traceSegment_049_0405_0033, g32p_row03_traceSegment_049_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 472 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 480 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 472 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 472 8 9, g32p_row03_traceSegment_049_0472_0008, g32p_row03_traceSegment_049_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 489 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 497 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 489 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 489 8 9, g32p_row03_traceSegment_049_0489_0008, g32p_row03_traceSegment_049_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 472 34 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 472 17 17, g32p_row03_traceSegment_049_0472_0017, g32p_row03_traceSegment_049_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 506 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 514 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 506 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 506 8 9, g32p_row03_traceSegment_049_0506_0008, g32p_row03_traceSegment_049_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 531 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 523 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 523 8 9, g32p_row03_traceSegment_049_0523_0008, g32p_row03_traceSegment_049_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 506 34 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 506 17 17, g32p_row03_traceSegment_049_0506_0017, g32p_row03_traceSegment_049_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 472 68 = [0, 0, 2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 472 34 34, g32p_row03_traceSegment_049_0472_0034, g32p_row03_traceSegment_049_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 405 135 = [0, 0, 4, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 405 67 68, g32p_row03_traceSegment_049_0405_0067, g32p_row03_traceSegment_049_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 270 270 = [0, 0, 5, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 270 135 135, g32p_row03_traceSegment_049_0270_0135, g32p_row03_traceSegment_049_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_049 0 540 = [0, 0, 18, 0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 0 270 270, g32p_row03_traceSegment_049_0000_0270, g32p_row03_traceSegment_049_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 556 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 564 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 556 17 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 556 8 9, g32p_row03_traceSegment_049_0556_0008, g32p_row03_traceSegment_049_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 540 33 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 540 16 17, g32p_row03_traceSegment_049_0540_0016, g32p_row03_traceSegment_049_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 573 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 573 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 573 8 9, g32p_row03_traceSegment_049_0573_0008, g32p_row03_traceSegment_049_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 590 8 9, g32p_row03_traceSegment_049_0590_0008, g32p_row03_traceSegment_049_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 573 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 573 17 17, g32p_row03_traceSegment_049_0573_0017, g32p_row03_traceSegment_049_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 540 67 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 540 33 34, g32p_row03_traceSegment_049_0540_0033, g32p_row03_traceSegment_049_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 607 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 615 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 607 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 607 8 9, g32p_row03_traceSegment_049_0607_0008, g32p_row03_traceSegment_049_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 624 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 632 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 624 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 624 8 9, g32p_row03_traceSegment_049_0624_0008, g32p_row03_traceSegment_049_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 607 34 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 607 17 17, g32p_row03_traceSegment_049_0607_0017, g32p_row03_traceSegment_049_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 641 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 649 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 641 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 641 8 9, g32p_row03_traceSegment_049_0641_0008, g32p_row03_traceSegment_049_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 666 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 658 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 658 8 9, g32p_row03_traceSegment_049_0658_0008, g32p_row03_traceSegment_049_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 641 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 641 17 17, g32p_row03_traceSegment_049_0641_0017, g32p_row03_traceSegment_049_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 607 68 = [0, 0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 607 34 34, g32p_row03_traceSegment_049_0607_0034, g32p_row03_traceSegment_049_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 540 135 = [0, 0, 7, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 540 67 68, g32p_row03_traceSegment_049_0540_0067, g32p_row03_traceSegment_049_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 675 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 691 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 699 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 691 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 691 8 9, g32p_row03_traceSegment_049_0691_0008, g32p_row03_traceSegment_049_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 675 33 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 675 16 17, g32p_row03_traceSegment_049_0675_0016, g32p_row03_traceSegment_049_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 708 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 716 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 708 17 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 708 8 9, g32p_row03_traceSegment_049_0708_0008, g32p_row03_traceSegment_049_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 725 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 725 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 725 8 9, g32p_row03_traceSegment_049_0725_0008, g32p_row03_traceSegment_049_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 708 34 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 708 17 17, g32p_row03_traceSegment_049_0708_0017, g32p_row03_traceSegment_049_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 675 67 = [0, 0, 6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 675 33 34, g32p_row03_traceSegment_049_0675_0033, g32p_row03_traceSegment_049_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 742 8 9, g32p_row03_traceSegment_049_0742_0008, g32p_row03_traceSegment_049_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 767 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 759 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 759 8 9, g32p_row03_traceSegment_049_0759_0008, g32p_row03_traceSegment_049_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 742 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 742 17 17, g32p_row03_traceSegment_049_0742_0017, g32p_row03_traceSegment_049_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 776 8 9, g32p_row03_traceSegment_049_0776_0008, g32p_row03_traceSegment_049_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 793 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 801 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 793 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 793 8 9, g32p_row03_traceSegment_049_0793_0008, g32p_row03_traceSegment_049_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 776 34 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 776 17 17, g32p_row03_traceSegment_049_0776_0017, g32p_row03_traceSegment_049_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 742 68 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 742 34 34, g32p_row03_traceSegment_049_0742_0034, g32p_row03_traceSegment_049_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 675 135 = [0, 0, 8, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 675 67 68, g32p_row03_traceSegment_049_0675_0067, g32p_row03_traceSegment_049_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 540 270 = [0, 0, 15, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 540 135 135, g32p_row03_traceSegment_049_0540_0135, g32p_row03_traceSegment_049_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 810 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 834 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 826 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 826 8 9, g32p_row03_traceSegment_049_0826_0008, g32p_row03_traceSegment_049_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 810 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 810 16 17, g32p_row03_traceSegment_049_0810_0016, g32p_row03_traceSegment_049_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 843 8 9, g32p_row03_traceSegment_049_0843_0008, g32p_row03_traceSegment_049_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 860 8 9, g32p_row03_traceSegment_049_0860_0008, g32p_row03_traceSegment_049_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 843 17 17, g32p_row03_traceSegment_049_0843_0017, g32p_row03_traceSegment_049_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 810 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 810 33 34, g32p_row03_traceSegment_049_0810_0033, g32p_row03_traceSegment_049_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 877 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 885 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 877 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 877 8 9, g32p_row03_traceSegment_049_0877_0008, g32p_row03_traceSegment_049_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 894 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 902 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 894 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 894 8 9, g32p_row03_traceSegment_049_0894_0008, g32p_row03_traceSegment_049_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 877 34 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 877 17 17, g32p_row03_traceSegment_049_0877_0017, g32p_row03_traceSegment_049_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 911 8 9, g32p_row03_traceSegment_049_0911_0008, g32p_row03_traceSegment_049_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 928 8 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 928 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 928 8 9, g32p_row03_traceSegment_049_0928_0008, g32p_row03_traceSegment_049_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 911 34 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 911 17 17, g32p_row03_traceSegment_049_0911_0017, g32p_row03_traceSegment_049_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 877 68 = [0, 0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 877 34 34, g32p_row03_traceSegment_049_0877_0034, g32p_row03_traceSegment_049_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 810 135 = [0, 0, 6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 810 67 68, g32p_row03_traceSegment_049_0810_0067, g32p_row03_traceSegment_049_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 945 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 969 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 961 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 961 8 9, g32p_row03_traceSegment_049_0961_0008, g32p_row03_traceSegment_049_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 945 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 945 16 17, g32p_row03_traceSegment_049_0945_0016, g32p_row03_traceSegment_049_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 978 8 9, g32p_row03_traceSegment_049_0978_0008, g32p_row03_traceSegment_049_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1003 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 995 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 995 8 9, g32p_row03_traceSegment_049_0995_0008, g32p_row03_traceSegment_049_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 978 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 978 17 17, g32p_row03_traceSegment_049_0978_0017, g32p_row03_traceSegment_049_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 945 67 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 945 33 34, g32p_row03_traceSegment_049_0945_0033, g32p_row03_traceSegment_049_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1020 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1012 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1012 8 9, g32p_row03_traceSegment_049_1012_0008, g32p_row03_traceSegment_049_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1029 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1037 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1029 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1029 8 9, g32p_row03_traceSegment_049_1029_0008, g32p_row03_traceSegment_049_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1012 34 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1012 17 17, g32p_row03_traceSegment_049_1012_0017, g32p_row03_traceSegment_049_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1046 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1046 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1046 8 9, g32p_row03_traceSegment_049_1046_0008, g32p_row03_traceSegment_049_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1063 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1063 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1063 8 9, g32p_row03_traceSegment_049_1063_0008, g32p_row03_traceSegment_049_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1046 34 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1046 17 17, g32p_row03_traceSegment_049_1046_0017, g32p_row03_traceSegment_049_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 1012 68 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1012 34 34, g32p_row03_traceSegment_049_1012_0034, g32p_row03_traceSegment_049_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 945 135 = [0, 0, 5, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 945 67 68, g32p_row03_traceSegment_049_0945_0067, g32p_row03_traceSegment_049_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 810 270 = [0, 0, 11, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 810 135 135, g32p_row03_traceSegment_049_0810_0135, g32p_row03_traceSegment_049_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_049 540 540 = [0, 0, 26, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 540 270 270, g32p_row03_traceSegment_049_0540_0270, g32p_row03_traceSegment_049_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_049 0 1080 = [0, 0, 44, 0, 0, 46] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 0 540 540, g32p_row03_traceSegment_049_0000_0540, g32p_row03_traceSegment_049_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 1080 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1096 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1104 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1096 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1096 8 9, g32p_row03_traceSegment_049_1096_0008, g32p_row03_traceSegment_049_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 1080 33 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1080 16 17, g32p_row03_traceSegment_049_1080_0016, g32p_row03_traceSegment_049_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1113 8 9, g32p_row03_traceSegment_049_1113_0008, g32p_row03_traceSegment_049_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1130 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1138 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1130 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1130 8 9, g32p_row03_traceSegment_049_1130_0008, g32p_row03_traceSegment_049_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1113 34 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1113 17 17, g32p_row03_traceSegment_049_1113_0017, g32p_row03_traceSegment_049_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 1080 67 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1080 33 34, g32p_row03_traceSegment_049_1080_0033, g32p_row03_traceSegment_049_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1147 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1147 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1147 8 9, g32p_row03_traceSegment_049_1147_0008, g32p_row03_traceSegment_049_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1164 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1172 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1164 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1164 8 9, g32p_row03_traceSegment_049_1164_0008, g32p_row03_traceSegment_049_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1147 34 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1147 17 17, g32p_row03_traceSegment_049_1147_0017, g32p_row03_traceSegment_049_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1181 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1181 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1181 8 9, g32p_row03_traceSegment_049_1181_0008, g32p_row03_traceSegment_049_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1206 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1198 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1198 8 9, g32p_row03_traceSegment_049_1198_0008, g32p_row03_traceSegment_049_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1181 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1181 17 17, g32p_row03_traceSegment_049_1181_0017, g32p_row03_traceSegment_049_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 1147 68 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1147 34 34, g32p_row03_traceSegment_049_1147_0034, g32p_row03_traceSegment_049_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 1080 135 = [0, 0, 4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1080 67 68, g32p_row03_traceSegment_049_1080_0067, g32p_row03_traceSegment_049_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 1215 16 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1239 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1231 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1231 8 9, g32p_row03_traceSegment_049_1231_0008, g32p_row03_traceSegment_049_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 1215 33 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1215 16 17, g32p_row03_traceSegment_049_1215_0016, g32p_row03_traceSegment_049_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1248 8 9, g32p_row03_traceSegment_049_1248_0008, g32p_row03_traceSegment_049_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1273 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1265 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1265 8 9, g32p_row03_traceSegment_049_1265_0008, g32p_row03_traceSegment_049_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1248 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1248 17 17, g32p_row03_traceSegment_049_1248_0017, g32p_row03_traceSegment_049_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 1215 67 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1215 33 34, g32p_row03_traceSegment_049_1215_0033, g32p_row03_traceSegment_049_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1290 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1282 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1282 8 9, g32p_row03_traceSegment_049_1282_0008, g32p_row03_traceSegment_049_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1307 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1299 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1299 8 9, g32p_row03_traceSegment_049_1299_0008, g32p_row03_traceSegment_049_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1282 34 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1282 17 17, g32p_row03_traceSegment_049_1282_0017, g32p_row03_traceSegment_049_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1316 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1324 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1316 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1316 8 9, g32p_row03_traceSegment_049_1316_0008, g32p_row03_traceSegment_049_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1333 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1341 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1333 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1333 8 9, g32p_row03_traceSegment_049_1333_0008, g32p_row03_traceSegment_049_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1316 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1316 17 17, g32p_row03_traceSegment_049_1316_0017, g32p_row03_traceSegment_049_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 1282 68 = [0, 0, 1, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1282 34 34, g32p_row03_traceSegment_049_1282_0034, g32p_row03_traceSegment_049_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 1215 135 = [0, 0, 2, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1215 67 68, g32p_row03_traceSegment_049_1215_0067, g32p_row03_traceSegment_049_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 1080 270 = [0, 0, 6, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1080 135 135, g32p_row03_traceSegment_049_1080_0135, g32p_row03_traceSegment_049_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 1350 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1374 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1366 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1366 8 9, g32p_row03_traceSegment_049_1366_0008, g32p_row03_traceSegment_049_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 1350 33 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1350 16 17, g32p_row03_traceSegment_049_1350_0016, g32p_row03_traceSegment_049_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1383 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1383 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1383 8 9, g32p_row03_traceSegment_049_1383_0008, g32p_row03_traceSegment_049_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1400 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1408 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1400 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1400 8 9, g32p_row03_traceSegment_049_1400_0008, g32p_row03_traceSegment_049_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1383 34 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1383 17 17, g32p_row03_traceSegment_049_1383_0017, g32p_row03_traceSegment_049_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 1350 67 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1350 33 34, g32p_row03_traceSegment_049_1350_0033, g32p_row03_traceSegment_049_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1417 8 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1417 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1417 8 9, g32p_row03_traceSegment_049_1417_0008, g32p_row03_traceSegment_049_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1434 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1442 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1434 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1434 8 9, g32p_row03_traceSegment_049_1434_0008, g32p_row03_traceSegment_049_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1417 34 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1417 17 17, g32p_row03_traceSegment_049_1417_0017, g32p_row03_traceSegment_049_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1451 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1451 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1451 8 9, g32p_row03_traceSegment_049_1451_0008, g32p_row03_traceSegment_049_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1468 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1476 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1468 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1468 8 9, g32p_row03_traceSegment_049_1468_0008, g32p_row03_traceSegment_049_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1451 34 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1451 17 17, g32p_row03_traceSegment_049_1451_0017, g32p_row03_traceSegment_049_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 1417 68 = [0, 0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1417 34 34, g32p_row03_traceSegment_049_1417_0034, g32p_row03_traceSegment_049_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 1350 135 = [0, 0, 5, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1350 67 68, g32p_row03_traceSegment_049_1350_0067, g32p_row03_traceSegment_049_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1509 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1501 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1501 8 9, g32p_row03_traceSegment_049_1501_0008, g32p_row03_traceSegment_049_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 1485 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1485 16 17, g32p_row03_traceSegment_049_1485_0016, g32p_row03_traceSegment_049_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1518 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1518 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1518 8 9, g32p_row03_traceSegment_049_1518_0008, g32p_row03_traceSegment_049_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1535 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1535 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1535 8 9, g32p_row03_traceSegment_049_1535_0008, g32p_row03_traceSegment_049_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1518 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1518 17 17, g32p_row03_traceSegment_049_1518_0017, g32p_row03_traceSegment_049_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 1485 67 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1485 33 34, g32p_row03_traceSegment_049_1485_0033, g32p_row03_traceSegment_049_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1560 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1552 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1552 8 9, g32p_row03_traceSegment_049_1552_0008, g32p_row03_traceSegment_049_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1577 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1569 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1569 8 9, g32p_row03_traceSegment_049_1569_0008, g32p_row03_traceSegment_049_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1552 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1552 17 17, g32p_row03_traceSegment_049_1552_0017, g32p_row03_traceSegment_049_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1586 8 9, g32p_row03_traceSegment_049_1586_0008, g32p_row03_traceSegment_049_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1603 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1611 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1603 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1603 8 9, g32p_row03_traceSegment_049_1603_0008, g32p_row03_traceSegment_049_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1586 34 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1586 17 17, g32p_row03_traceSegment_049_1586_0017, g32p_row03_traceSegment_049_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 1552 68 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1552 34 34, g32p_row03_traceSegment_049_1552_0034, g32p_row03_traceSegment_049_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 1485 135 = [0, 0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1485 67 68, g32p_row03_traceSegment_049_1485_0067, g32p_row03_traceSegment_049_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 1350 270 = [0, 0, 10, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1350 135 135, g32p_row03_traceSegment_049_1350_0135, g32p_row03_traceSegment_049_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_049 1080 540 = [0, 0, 16, 0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1080 270 270, g32p_row03_traceSegment_049_1080_0270, g32p_row03_traceSegment_049_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 1620 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1636 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1636 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1636 8 9, g32p_row03_traceSegment_049_1636_0008, g32p_row03_traceSegment_049_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 1620 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1620 16 17, g32p_row03_traceSegment_049_1620_0016, g32p_row03_traceSegment_049_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1653 8 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1653 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1653 8 9, g32p_row03_traceSegment_049_1653_0008, g32p_row03_traceSegment_049_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1670 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1678 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1670 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1670 8 9, g32p_row03_traceSegment_049_1670_0008, g32p_row03_traceSegment_049_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1653 34 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1653 17 17, g32p_row03_traceSegment_049_1653_0017, g32p_row03_traceSegment_049_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 1620 67 = [0, 0, 5, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1620 33 34, g32p_row03_traceSegment_049_1620_0033, g32p_row03_traceSegment_049_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1687 8 9, g32p_row03_traceSegment_049_1687_0008, g32p_row03_traceSegment_049_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1704 8 9, g32p_row03_traceSegment_049_1704_0008, g32p_row03_traceSegment_049_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1687 17 17, g32p_row03_traceSegment_049_1687_0017, g32p_row03_traceSegment_049_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1721 8 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1721 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1721 8 9, g32p_row03_traceSegment_049_1721_0008, g32p_row03_traceSegment_049_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1738 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1746 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1738 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1738 8 9, g32p_row03_traceSegment_049_1738_0008, g32p_row03_traceSegment_049_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1721 34 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1721 17 17, g32p_row03_traceSegment_049_1721_0017, g32p_row03_traceSegment_049_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 1687 68 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1687 34 34, g32p_row03_traceSegment_049_1687_0034, g32p_row03_traceSegment_049_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 1620 135 = [0, 0, 8, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1620 67 68, g32p_row03_traceSegment_049_1620_0067, g32p_row03_traceSegment_049_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 1755 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1779 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1771 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1771 8 9, g32p_row03_traceSegment_049_1771_0008, g32p_row03_traceSegment_049_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 1755 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1755 16 17, g32p_row03_traceSegment_049_1755_0016, g32p_row03_traceSegment_049_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1788 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1796 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1788 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1788 8 9, g32p_row03_traceSegment_049_1788_0008, g32p_row03_traceSegment_049_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1805 8 9, g32p_row03_traceSegment_049_1805_0008, g32p_row03_traceSegment_049_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1788 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1788 17 17, g32p_row03_traceSegment_049_1788_0017, g32p_row03_traceSegment_049_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 1755 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1755 33 34, g32p_row03_traceSegment_049_1755_0033, g32p_row03_traceSegment_049_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1822 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1830 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1822 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1822 8 9, g32p_row03_traceSegment_049_1822_0008, g32p_row03_traceSegment_049_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1839 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1847 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1839 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1839 8 9, g32p_row03_traceSegment_049_1839_0008, g32p_row03_traceSegment_049_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1822 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1822 17 17, g32p_row03_traceSegment_049_1822_0017, g32p_row03_traceSegment_049_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1856 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1856 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1856 8 9, g32p_row03_traceSegment_049_1856_0008, g32p_row03_traceSegment_049_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1873 8 9, g32p_row03_traceSegment_049_1873_0008, g32p_row03_traceSegment_049_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1856 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1856 17 17, g32p_row03_traceSegment_049_1856_0017, g32p_row03_traceSegment_049_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 1822 68 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1822 34 34, g32p_row03_traceSegment_049_1822_0034, g32p_row03_traceSegment_049_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 1755 135 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1755 67 68, g32p_row03_traceSegment_049_1755_0067, g32p_row03_traceSegment_049_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 1620 270 = [0, 0, 17, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1620 135 135, g32p_row03_traceSegment_049_1620_0135, g32p_row03_traceSegment_049_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 1890 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1906 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1914 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1906 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1906 8 9, g32p_row03_traceSegment_049_1906_0008, g32p_row03_traceSegment_049_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 1890 33 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1890 16 17, g32p_row03_traceSegment_049_1890_0016, g32p_row03_traceSegment_049_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1931 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1923 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1923 8 9, g32p_row03_traceSegment_049_1923_0008, g32p_row03_traceSegment_049_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1948 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1940 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1940 8 9, g32p_row03_traceSegment_049_1940_0008, g32p_row03_traceSegment_049_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1923 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1923 17 17, g32p_row03_traceSegment_049_1923_0017, g32p_row03_traceSegment_049_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 1890 67 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1890 33 34, g32p_row03_traceSegment_049_1890_0033, g32p_row03_traceSegment_049_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1957 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1957 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1957 8 9, g32p_row03_traceSegment_049_1957_0008, g32p_row03_traceSegment_049_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1974 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1982 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1974 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1974 8 9, g32p_row03_traceSegment_049_1974_0008, g32p_row03_traceSegment_049_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1957 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1957 17 17, g32p_row03_traceSegment_049_1957_0017, g32p_row03_traceSegment_049_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 1991 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 1999 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 1991 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1991 8 9, g32p_row03_traceSegment_049_1991_0008, g32p_row03_traceSegment_049_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2008 8 9, g32p_row03_traceSegment_049_2008_0008, g32p_row03_traceSegment_049_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 1991 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1991 17 17, g32p_row03_traceSegment_049_1991_0017, g32p_row03_traceSegment_049_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 1957 68 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1957 34 34, g32p_row03_traceSegment_049_1957_0034, g32p_row03_traceSegment_049_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 1890 135 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1890 67 68, g32p_row03_traceSegment_049_1890_0067, g32p_row03_traceSegment_049_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2041 8 9, g32p_row03_traceSegment_049_2041_0008, g32p_row03_traceSegment_049_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2025 16 17, g32p_row03_traceSegment_049_2025_0016, g32p_row03_traceSegment_049_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2058 8 9, g32p_row03_traceSegment_049_2058_0008, g32p_row03_traceSegment_049_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2075 8 9, g32p_row03_traceSegment_049_2075_0008, g32p_row03_traceSegment_049_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2058 17 17, g32p_row03_traceSegment_049_2058_0017, g32p_row03_traceSegment_049_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2025 33 34, g32p_row03_traceSegment_049_2025_0033, g32p_row03_traceSegment_049_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2092 8 9, g32p_row03_traceSegment_049_2092_0008, g32p_row03_traceSegment_049_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2109 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2109 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2109 8 9, g32p_row03_traceSegment_049_2109_0008, g32p_row03_traceSegment_049_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2092 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2092 17 17, g32p_row03_traceSegment_049_2092_0017, g32p_row03_traceSegment_049_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2126 8 9, g32p_row03_traceSegment_049_2126_0008, g32p_row03_traceSegment_049_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2151 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2143 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2143 8 9, g32p_row03_traceSegment_049_2143_0008, g32p_row03_traceSegment_049_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2126 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2126 17 17, g32p_row03_traceSegment_049_2126_0017, g32p_row03_traceSegment_049_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 2092 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2092 34 34, g32p_row03_traceSegment_049_2092_0034, g32p_row03_traceSegment_049_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 2025 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2025 67 68, g32p_row03_traceSegment_049_2025_0067, g32p_row03_traceSegment_049_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 1890 270 = [0, 0, 14, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1890 135 135, g32p_row03_traceSegment_049_1890_0135, g32p_row03_traceSegment_049_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_049 1620 540 = [0, 0, 31, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1620 270 270, g32p_row03_traceSegment_049_1620_0270, g32p_row03_traceSegment_049_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_049_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_049 1080 1080 = [0, 0, 47, 0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 1080 540 540, g32p_row03_traceSegment_049_1080_0540, g32p_row03_traceSegment_049_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_049 0 2160 = [0, 0, 91, 0, 0, 75] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 0 1080 1080, g32p_row03_traceSegment_049_0000_1080, g32p_row03_traceSegment_049_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2176 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2184 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2176 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2176 8 9, g32p_row03_traceSegment_049_2176_0008, g32p_row03_traceSegment_049_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 2160 33 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2160 16 17, g32p_row03_traceSegment_049_2160_0016, g32p_row03_traceSegment_049_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2193 8 9, g32p_row03_traceSegment_049_2193_0008, g32p_row03_traceSegment_049_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2210 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2210 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2210 8 9, g32p_row03_traceSegment_049_2210_0008, g32p_row03_traceSegment_049_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2193 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2193 17 17, g32p_row03_traceSegment_049_2193_0017, g32p_row03_traceSegment_049_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 2160 67 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2160 33 34, g32p_row03_traceSegment_049_2160_0033, g32p_row03_traceSegment_049_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2227 8 9, g32p_row03_traceSegment_049_2227_0008, g32p_row03_traceSegment_049_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2244 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2252 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2244 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2244 8 9, g32p_row03_traceSegment_049_2244_0008, g32p_row03_traceSegment_049_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2227 34 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2227 17 17, g32p_row03_traceSegment_049_2227_0017, g32p_row03_traceSegment_049_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2261 8 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2269 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2261 17 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2261 8 9, g32p_row03_traceSegment_049_2261_0008, g32p_row03_traceSegment_049_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2286 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2278 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2278 8 9, g32p_row03_traceSegment_049_2278_0008, g32p_row03_traceSegment_049_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2261 34 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2261 17 17, g32p_row03_traceSegment_049_2261_0017, g32p_row03_traceSegment_049_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 2227 68 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2227 34 34, g32p_row03_traceSegment_049_2227_0034, g32p_row03_traceSegment_049_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 2160 135 = [0, 0, 3, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2160 67 68, g32p_row03_traceSegment_049_2160_0067, g32p_row03_traceSegment_049_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2311 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2319 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2311 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2311 8 9, g32p_row03_traceSegment_049_2311_0008, g32p_row03_traceSegment_049_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 2295 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2295 16 17, g32p_row03_traceSegment_049_2295_0016, g32p_row03_traceSegment_049_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2328 8 9, g32p_row03_traceSegment_049_2328_0008, g32p_row03_traceSegment_049_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2345 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2345 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2345 8 9, g32p_row03_traceSegment_049_2345_0008, g32p_row03_traceSegment_049_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2328 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2328 17 17, g32p_row03_traceSegment_049_2328_0017, g32p_row03_traceSegment_049_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 2295 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2295 33 34, g32p_row03_traceSegment_049_2295_0033, g32p_row03_traceSegment_049_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2362 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2370 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2362 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2362 8 9, g32p_row03_traceSegment_049_2362_0008, g32p_row03_traceSegment_049_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2387 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2379 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2379 8 9, g32p_row03_traceSegment_049_2379_0008, g32p_row03_traceSegment_049_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2362 34 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2362 17 17, g32p_row03_traceSegment_049_2362_0017, g32p_row03_traceSegment_049_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2396 8 9, g32p_row03_traceSegment_049_2396_0008, g32p_row03_traceSegment_049_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2421 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2413 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2413 8 9, g32p_row03_traceSegment_049_2413_0008, g32p_row03_traceSegment_049_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2396 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2396 17 17, g32p_row03_traceSegment_049_2396_0017, g32p_row03_traceSegment_049_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 2362 68 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2362 34 34, g32p_row03_traceSegment_049_2362_0034, g32p_row03_traceSegment_049_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 2295 135 = [0, 0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2295 67 68, g32p_row03_traceSegment_049_2295_0067, g32p_row03_traceSegment_049_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 2160 270 = [0, 0, 4, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2160 135 135, g32p_row03_traceSegment_049_2160_0135, g32p_row03_traceSegment_049_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2454 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2446 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2446 8 9, g32p_row03_traceSegment_049_2446_0008, g32p_row03_traceSegment_049_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 2430 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2430 16 17, g32p_row03_traceSegment_049_2430_0016, g32p_row03_traceSegment_049_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2471 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2463 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2463 8 9, g32p_row03_traceSegment_049_2463_0008, g32p_row03_traceSegment_049_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2480 8 9, g32p_row03_traceSegment_049_2480_0008, g32p_row03_traceSegment_049_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2463 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2463 17 17, g32p_row03_traceSegment_049_2463_0017, g32p_row03_traceSegment_049_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 2430 67 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2430 33 34, g32p_row03_traceSegment_049_2430_0033, g32p_row03_traceSegment_049_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2497 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2505 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2497 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2497 8 9, g32p_row03_traceSegment_049_2497_0008, g32p_row03_traceSegment_049_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2514 8 9, g32p_row03_traceSegment_049_2514_0008, g32p_row03_traceSegment_049_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2497 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2497 17 17, g32p_row03_traceSegment_049_2497_0017, g32p_row03_traceSegment_049_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2531 8 9, g32p_row03_traceSegment_049_2531_0008, g32p_row03_traceSegment_049_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2548 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2556 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2548 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2548 8 9, g32p_row03_traceSegment_049_2548_0008, g32p_row03_traceSegment_049_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2531 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2531 17 17, g32p_row03_traceSegment_049_2531_0017, g32p_row03_traceSegment_049_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 2497 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2497 34 34, g32p_row03_traceSegment_049_2497_0034, g32p_row03_traceSegment_049_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 2430 135 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2430 67 68, g32p_row03_traceSegment_049_2430_0067, g32p_row03_traceSegment_049_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 2565 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2589 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2581 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2581 8 9, g32p_row03_traceSegment_049_2581_0008, g32p_row03_traceSegment_049_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 2565 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2565 16 17, g32p_row03_traceSegment_049_2565_0016, g32p_row03_traceSegment_049_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2606 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2598 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2598 8 9, g32p_row03_traceSegment_049_2598_0008, g32p_row03_traceSegment_049_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2623 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2615 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2615 8 9, g32p_row03_traceSegment_049_2615_0008, g32p_row03_traceSegment_049_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2598 34 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2598 17 17, g32p_row03_traceSegment_049_2598_0017, g32p_row03_traceSegment_049_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 2565 67 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2565 33 34, g32p_row03_traceSegment_049_2565_0033, g32p_row03_traceSegment_049_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2632 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2640 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2632 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2632 8 9, g32p_row03_traceSegment_049_2632_0008, g32p_row03_traceSegment_049_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2657 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2649 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2649 8 9, g32p_row03_traceSegment_049_2649_0008, g32p_row03_traceSegment_049_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2632 34 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2632 17 17, g32p_row03_traceSegment_049_2632_0017, g32p_row03_traceSegment_049_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2666 8 9, g32p_row03_traceSegment_049_2666_0008, g32p_row03_traceSegment_049_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2691 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2683 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2683 8 9, g32p_row03_traceSegment_049_2683_0008, g32p_row03_traceSegment_049_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2666 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2666 17 17, g32p_row03_traceSegment_049_2666_0017, g32p_row03_traceSegment_049_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 2632 68 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2632 34 34, g32p_row03_traceSegment_049_2632_0034, g32p_row03_traceSegment_049_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 2565 135 = [0, 0, 2, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2565 67 68, g32p_row03_traceSegment_049_2565_0067, g32p_row03_traceSegment_049_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 2430 270 = [0, 0, 2, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2430 135 135, g32p_row03_traceSegment_049_2430_0135, g32p_row03_traceSegment_049_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_049 2160 540 = [0, 0, 6, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2160 270 270, g32p_row03_traceSegment_049_2160_0270, g32p_row03_traceSegment_049_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 2700 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2716 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2724 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2716 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2716 8 9, g32p_row03_traceSegment_049_2716_0008, g32p_row03_traceSegment_049_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 2700 33 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2700 16 17, g32p_row03_traceSegment_049_2700_0016, g32p_row03_traceSegment_049_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2733 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2741 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2733 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2733 8 9, g32p_row03_traceSegment_049_2733_0008, g32p_row03_traceSegment_049_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2750 8 9, g32p_row03_traceSegment_049_2750_0008, g32p_row03_traceSegment_049_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2733 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2733 17 17, g32p_row03_traceSegment_049_2733_0017, g32p_row03_traceSegment_049_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 2700 67 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2700 33 34, g32p_row03_traceSegment_049_2700_0033, g32p_row03_traceSegment_049_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2767 8 9, g32p_row03_traceSegment_049_2767_0008, g32p_row03_traceSegment_049_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2784 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2792 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2784 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2784 8 9, g32p_row03_traceSegment_049_2784_0008, g32p_row03_traceSegment_049_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2767 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2767 17 17, g32p_row03_traceSegment_049_2767_0017, g32p_row03_traceSegment_049_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2801 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2809 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2801 17 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2801 8 9, g32p_row03_traceSegment_049_2801_0008, g32p_row03_traceSegment_049_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2818 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2826 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2818 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2818 8 9, g32p_row03_traceSegment_049_2818_0008, g32p_row03_traceSegment_049_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2801 34 = [0, 0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2801 17 17, g32p_row03_traceSegment_049_2801_0017, g32p_row03_traceSegment_049_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 2767 68 = [0, 0, 1, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2767 34 34, g32p_row03_traceSegment_049_2767_0034, g32p_row03_traceSegment_049_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 2700 135 = [0, 0, 1, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2700 67 68, g32p_row03_traceSegment_049_2700_0067, g32p_row03_traceSegment_049_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 2835 16 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2851 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2859 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2851 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2851 8 9, g32p_row03_traceSegment_049_2851_0008, g32p_row03_traceSegment_049_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 2835 33 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2835 16 17, g32p_row03_traceSegment_049_2835_0016, g32p_row03_traceSegment_049_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2876 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2868 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2868 8 9, g32p_row03_traceSegment_049_2868_0008, g32p_row03_traceSegment_049_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2885 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2893 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2885 17 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2885 8 9, g32p_row03_traceSegment_049_2885_0008, g32p_row03_traceSegment_049_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2868 34 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2868 17 17, g32p_row03_traceSegment_049_2868_0017, g32p_row03_traceSegment_049_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 2835 67 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2835 33 34, g32p_row03_traceSegment_049_2835_0033, g32p_row03_traceSegment_049_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2902 8 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2910 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2902 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2902 8 9, g32p_row03_traceSegment_049_2902_0008, g32p_row03_traceSegment_049_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2919 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2919 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2919 8 9, g32p_row03_traceSegment_049_2919_0008, g32p_row03_traceSegment_049_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2902 34 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2902 17 17, g32p_row03_traceSegment_049_2902_0017, g32p_row03_traceSegment_049_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2944 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2936 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2936 8 9, g32p_row03_traceSegment_049_2936_0008, g32p_row03_traceSegment_049_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2953 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2961 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2953 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2953 8 9, g32p_row03_traceSegment_049_2953_0008, g32p_row03_traceSegment_049_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 2936 34 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2936 17 17, g32p_row03_traceSegment_049_2936_0017, g32p_row03_traceSegment_049_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 2902 68 = [0, 0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2902 34 34, g32p_row03_traceSegment_049_2902_0034, g32p_row03_traceSegment_049_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 2835 135 = [0, 0, 1, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2835 67 68, g32p_row03_traceSegment_049_2835_0067, g32p_row03_traceSegment_049_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 2700 270 = [0, 0, 2, 0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2700 135 135, g32p_row03_traceSegment_049_2700_0135, g32p_row03_traceSegment_049_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 2970 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 2994 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 2986 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2986 8 9, g32p_row03_traceSegment_049_2986_0008, g32p_row03_traceSegment_049_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 2970 33 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2970 16 17, g32p_row03_traceSegment_049_2970_0016, g32p_row03_traceSegment_049_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3011 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3003 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3003 8 9, g32p_row03_traceSegment_049_3003_0008, g32p_row03_traceSegment_049_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3020 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3020 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3020 8 9, g32p_row03_traceSegment_049_3020_0008, g32p_row03_traceSegment_049_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3003 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3003 17 17, g32p_row03_traceSegment_049_3003_0017, g32p_row03_traceSegment_049_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 2970 67 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2970 33 34, g32p_row03_traceSegment_049_2970_0033, g32p_row03_traceSegment_049_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3037 8 9, g32p_row03_traceSegment_049_3037_0008, g32p_row03_traceSegment_049_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3062 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3054 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3054 8 9, g32p_row03_traceSegment_049_3054_0008, g32p_row03_traceSegment_049_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3037 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3037 17 17, g32p_row03_traceSegment_049_3037_0017, g32p_row03_traceSegment_049_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3071 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3071 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3071 8 9, g32p_row03_traceSegment_049_3071_0008, g32p_row03_traceSegment_049_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3088 8 9, g32p_row03_traceSegment_049_3088_0008, g32p_row03_traceSegment_049_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3071 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3071 17 17, g32p_row03_traceSegment_049_3071_0017, g32p_row03_traceSegment_049_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 3037 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3037 34 34, g32p_row03_traceSegment_049_3037_0034, g32p_row03_traceSegment_049_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 2970 135 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2970 67 68, g32p_row03_traceSegment_049_2970_0067, g32p_row03_traceSegment_049_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 3105 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3129 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3121 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3121 8 9, g32p_row03_traceSegment_049_3121_0008, g32p_row03_traceSegment_049_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 3105 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3105 16 17, g32p_row03_traceSegment_049_3105_0016, g32p_row03_traceSegment_049_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3138 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3146 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3138 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3138 8 9, g32p_row03_traceSegment_049_3138_0008, g32p_row03_traceSegment_049_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3163 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3155 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3155 8 9, g32p_row03_traceSegment_049_3155_0008, g32p_row03_traceSegment_049_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3138 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3138 17 17, g32p_row03_traceSegment_049_3138_0017, g32p_row03_traceSegment_049_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 3105 67 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3105 33 34, g32p_row03_traceSegment_049_3105_0033, g32p_row03_traceSegment_049_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3180 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3172 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3172 8 9, g32p_row03_traceSegment_049_3172_0008, g32p_row03_traceSegment_049_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3189 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3189 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3189 8 9, g32p_row03_traceSegment_049_3189_0008, g32p_row03_traceSegment_049_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3172 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3172 17 17, g32p_row03_traceSegment_049_3172_0017, g32p_row03_traceSegment_049_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3214 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3206 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3206 8 9, g32p_row03_traceSegment_049_3206_0008, g32p_row03_traceSegment_049_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3231 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3223 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3223 8 9, g32p_row03_traceSegment_049_3223_0008, g32p_row03_traceSegment_049_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3206 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3206 17 17, g32p_row03_traceSegment_049_3206_0017, g32p_row03_traceSegment_049_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 3172 68 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3172 34 34, g32p_row03_traceSegment_049_3172_0034, g32p_row03_traceSegment_049_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 3105 135 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3105 67 68, g32p_row03_traceSegment_049_3105_0067, g32p_row03_traceSegment_049_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 2970 270 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2970 135 135, g32p_row03_traceSegment_049_2970_0135, g32p_row03_traceSegment_049_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_049 2700 540 = [0, 0, 21, 0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2700 270 270, g32p_row03_traceSegment_049_2700_0270, g32p_row03_traceSegment_049_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_049 2160 1080 = [0, 0, 27, 0, 0, 66] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2160 540 540, g32p_row03_traceSegment_049_2160_0540, g32p_row03_traceSegment_049_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 3240 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3256 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3264 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3256 17 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3256 8 9, g32p_row03_traceSegment_049_3256_0008, g32p_row03_traceSegment_049_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 3240 33 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3240 16 17, g32p_row03_traceSegment_049_3240_0016, g32p_row03_traceSegment_049_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3273 8 9, g32p_row03_traceSegment_049_3273_0008, g32p_row03_traceSegment_049_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3290 8 9, g32p_row03_traceSegment_049_3290_0008, g32p_row03_traceSegment_049_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3273 17 17, g32p_row03_traceSegment_049_3273_0017, g32p_row03_traceSegment_049_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 3240 67 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3240 33 34, g32p_row03_traceSegment_049_3240_0033, g32p_row03_traceSegment_049_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3307 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3315 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3307 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3307 8 9, g32p_row03_traceSegment_049_3307_0008, g32p_row03_traceSegment_049_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3324 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3332 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3324 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3324 8 9, g32p_row03_traceSegment_049_3324_0008, g32p_row03_traceSegment_049_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3307 34 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3307 17 17, g32p_row03_traceSegment_049_3307_0017, g32p_row03_traceSegment_049_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3341 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3349 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3341 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3341 8 9, g32p_row03_traceSegment_049_3341_0008, g32p_row03_traceSegment_049_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3358 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3366 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3358 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3358 8 9, g32p_row03_traceSegment_049_3358_0008, g32p_row03_traceSegment_049_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3341 34 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3341 17 17, g32p_row03_traceSegment_049_3341_0017, g32p_row03_traceSegment_049_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 3307 68 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3307 34 34, g32p_row03_traceSegment_049_3307_0034, g32p_row03_traceSegment_049_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 3240 135 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3240 67 68, g32p_row03_traceSegment_049_3240_0067, g32p_row03_traceSegment_049_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 3375 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3391 8 9, g32p_row03_traceSegment_049_3391_0008, g32p_row03_traceSegment_049_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 3375 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3375 16 17, g32p_row03_traceSegment_049_3375_0016, g32p_row03_traceSegment_049_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3416 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3408 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3408 8 9, g32p_row03_traceSegment_049_3408_0008, g32p_row03_traceSegment_049_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3425 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3433 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3425 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3425 8 9, g32p_row03_traceSegment_049_3425_0008, g32p_row03_traceSegment_049_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3408 34 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3408 17 17, g32p_row03_traceSegment_049_3408_0017, g32p_row03_traceSegment_049_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 3375 67 = [0, 0, 5, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3375 33 34, g32p_row03_traceSegment_049_3375_0033, g32p_row03_traceSegment_049_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3442 8 9, g32p_row03_traceSegment_049_3442_0008, g32p_row03_traceSegment_049_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3467 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3459 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3459 8 9, g32p_row03_traceSegment_049_3459_0008, g32p_row03_traceSegment_049_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3442 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3442 17 17, g32p_row03_traceSegment_049_3442_0017, g32p_row03_traceSegment_049_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3476 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3476 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3476 8 9, g32p_row03_traceSegment_049_3476_0008, g32p_row03_traceSegment_049_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3501 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3493 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3493 8 9, g32p_row03_traceSegment_049_3493_0008, g32p_row03_traceSegment_049_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3476 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3476 17 17, g32p_row03_traceSegment_049_3476_0017, g32p_row03_traceSegment_049_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 3442 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3442 34 34, g32p_row03_traceSegment_049_3442_0034, g32p_row03_traceSegment_049_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 3375 135 = [0, 0, 9, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3375 67 68, g32p_row03_traceSegment_049_3375_0067, g32p_row03_traceSegment_049_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 3240 270 = [0, 0, 24, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3240 135 135, g32p_row03_traceSegment_049_3240_0135, g32p_row03_traceSegment_049_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 3510 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3526 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3526 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3526 8 9, g32p_row03_traceSegment_049_3526_0008, g32p_row03_traceSegment_049_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 3510 33 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3510 16 17, g32p_row03_traceSegment_049_3510_0016, g32p_row03_traceSegment_049_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3543 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3543 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3543 8 9, g32p_row03_traceSegment_049_3543_0008, g32p_row03_traceSegment_049_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3560 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3560 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3560 8 9, g32p_row03_traceSegment_049_3560_0008, g32p_row03_traceSegment_049_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3543 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3543 17 17, g32p_row03_traceSegment_049_3543_0017, g32p_row03_traceSegment_049_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 3510 67 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3510 33 34, g32p_row03_traceSegment_049_3510_0033, g32p_row03_traceSegment_049_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3577 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3585 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3577 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3577 8 9, g32p_row03_traceSegment_049_3577_0008, g32p_row03_traceSegment_049_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3594 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3594 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3594 8 9, g32p_row03_traceSegment_049_3594_0008, g32p_row03_traceSegment_049_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3577 34 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3577 17 17, g32p_row03_traceSegment_049_3577_0017, g32p_row03_traceSegment_049_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3611 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3619 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3611 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3611 8 9, g32p_row03_traceSegment_049_3611_0008, g32p_row03_traceSegment_049_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3628 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3628 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3628 8 9, g32p_row03_traceSegment_049_3628_0008, g32p_row03_traceSegment_049_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3611 34 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3611 17 17, g32p_row03_traceSegment_049_3611_0017, g32p_row03_traceSegment_049_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 3577 68 = [0, 0, 7, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3577 34 34, g32p_row03_traceSegment_049_3577_0034, g32p_row03_traceSegment_049_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 3510 135 = [0, 0, 10, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3510 67 68, g32p_row03_traceSegment_049_3510_0067, g32p_row03_traceSegment_049_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 3645 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3661 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3661 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3661 8 9, g32p_row03_traceSegment_049_3661_0008, g32p_row03_traceSegment_049_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 3645 33 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3645 16 17, g32p_row03_traceSegment_049_3645_0016, g32p_row03_traceSegment_049_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3678 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3686 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3678 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3678 8 9, g32p_row03_traceSegment_049_3678_0008, g32p_row03_traceSegment_049_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3695 8 9, g32p_row03_traceSegment_049_3695_0008, g32p_row03_traceSegment_049_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3678 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3678 17 17, g32p_row03_traceSegment_049_3678_0017, g32p_row03_traceSegment_049_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 3645 67 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3645 33 34, g32p_row03_traceSegment_049_3645_0033, g32p_row03_traceSegment_049_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3712 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3720 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3712 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3712 8 9, g32p_row03_traceSegment_049_3712_0008, g32p_row03_traceSegment_049_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3729 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3729 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3729 8 9, g32p_row03_traceSegment_049_3729_0008, g32p_row03_traceSegment_049_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3712 34 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3712 17 17, g32p_row03_traceSegment_049_3712_0017, g32p_row03_traceSegment_049_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3754 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3746 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3746 8 9, g32p_row03_traceSegment_049_3746_0008, g32p_row03_traceSegment_049_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3763 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3771 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3763 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3763 8 9, g32p_row03_traceSegment_049_3763_0008, g32p_row03_traceSegment_049_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3746 34 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3746 17 17, g32p_row03_traceSegment_049_3746_0017, g32p_row03_traceSegment_049_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 3712 68 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3712 34 34, g32p_row03_traceSegment_049_3712_0034, g32p_row03_traceSegment_049_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 3645 135 = [0, 0, 9, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3645 67 68, g32p_row03_traceSegment_049_3645_0067, g32p_row03_traceSegment_049_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 3510 270 = [0, 0, 19, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3510 135 135, g32p_row03_traceSegment_049_3510_0135, g32p_row03_traceSegment_049_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_049 3240 540 = [0, 0, 43, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3240 270 270, g32p_row03_traceSegment_049_3240_0270, g32p_row03_traceSegment_049_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 3780 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3796 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3804 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3796 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3796 8 9, g32p_row03_traceSegment_049_3796_0008, g32p_row03_traceSegment_049_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 3780 33 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3780 16 17, g32p_row03_traceSegment_049_3780_0016, g32p_row03_traceSegment_049_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3813 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3813 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3813 8 9, g32p_row03_traceSegment_049_3813_0008, g32p_row03_traceSegment_049_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3830 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3830 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3830 8 9, g32p_row03_traceSegment_049_3830_0008, g32p_row03_traceSegment_049_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3813 34 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3813 17 17, g32p_row03_traceSegment_049_3813_0017, g32p_row03_traceSegment_049_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 3780 67 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3780 33 34, g32p_row03_traceSegment_049_3780_0033, g32p_row03_traceSegment_049_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3855 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3847 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3847 8 9, g32p_row03_traceSegment_049_3847_0008, g32p_row03_traceSegment_049_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3864 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3872 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3864 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3864 8 9, g32p_row03_traceSegment_049_3864_0008, g32p_row03_traceSegment_049_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3847 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3847 17 17, g32p_row03_traceSegment_049_3847_0017, g32p_row03_traceSegment_049_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3881 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3881 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3881 8 9, g32p_row03_traceSegment_049_3881_0008, g32p_row03_traceSegment_049_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3898 8 9, g32p_row03_traceSegment_049_3898_0008, g32p_row03_traceSegment_049_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3881 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3881 17 17, g32p_row03_traceSegment_049_3881_0017, g32p_row03_traceSegment_049_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 3847 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3847 34 34, g32p_row03_traceSegment_049_3847_0034, g32p_row03_traceSegment_049_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 3780 135 = [0, 0, 3, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3780 67 68, g32p_row03_traceSegment_049_3780_0067, g32p_row03_traceSegment_049_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 3915 16 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3931 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3939 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3931 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3931 8 9, g32p_row03_traceSegment_049_3931_0008, g32p_row03_traceSegment_049_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 3915 33 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3915 16 17, g32p_row03_traceSegment_049_3915_0016, g32p_row03_traceSegment_049_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3948 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3956 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3948 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3948 8 9, g32p_row03_traceSegment_049_3948_0008, g32p_row03_traceSegment_049_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3965 8 9, g32p_row03_traceSegment_049_3965_0008, g32p_row03_traceSegment_049_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3948 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3948 17 17, g32p_row03_traceSegment_049_3948_0017, g32p_row03_traceSegment_049_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 3915 67 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3915 33 34, g32p_row03_traceSegment_049_3915_0033, g32p_row03_traceSegment_049_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3982 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 3990 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3982 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3982 8 9, g32p_row03_traceSegment_049_3982_0008, g32p_row03_traceSegment_049_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 3999 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4007 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 3999 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3999 8 9, g32p_row03_traceSegment_049_3999_0008, g32p_row03_traceSegment_049_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 3982 34 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3982 17 17, g32p_row03_traceSegment_049_3982_0017, g32p_row03_traceSegment_049_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4016 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4024 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4016 17 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4016 8 9, g32p_row03_traceSegment_049_4016_0008, g32p_row03_traceSegment_049_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4033 8 9, g32p_row03_traceSegment_049_4033_0008, g32p_row03_traceSegment_049_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 4016 34 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4016 17 17, g32p_row03_traceSegment_049_4016_0017, g32p_row03_traceSegment_049_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 3982 68 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3982 34 34, g32p_row03_traceSegment_049_3982_0034, g32p_row03_traceSegment_049_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 3915 135 = [0, 0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3915 67 68, g32p_row03_traceSegment_049_3915_0067, g32p_row03_traceSegment_049_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 3780 270 = [0, 0, 3, 0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3780 135 135, g32p_row03_traceSegment_049_3780_0135, g32p_row03_traceSegment_049_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 4050 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4066 8 9, g32p_row03_traceSegment_049_4066_0008, g32p_row03_traceSegment_049_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 4050 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4050 16 17, g32p_row03_traceSegment_049_4050_0016, g32p_row03_traceSegment_049_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4083 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4091 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4083 17 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4083 8 9, g32p_row03_traceSegment_049_4083_0008, g32p_row03_traceSegment_049_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4100 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4100 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4100 8 9, g32p_row03_traceSegment_049_4100_0008, g32p_row03_traceSegment_049_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 4083 34 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4083 17 17, g32p_row03_traceSegment_049_4083_0017, g32p_row03_traceSegment_049_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 4050 67 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4050 33 34, g32p_row03_traceSegment_049_4050_0033, g32p_row03_traceSegment_049_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4117 8 9, g32p_row03_traceSegment_049_4117_0008, g32p_row03_traceSegment_049_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4134 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4134 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4134 8 9, g32p_row03_traceSegment_049_4134_0008, g32p_row03_traceSegment_049_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 4117 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4117 17 17, g32p_row03_traceSegment_049_4117_0017, g32p_row03_traceSegment_049_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4151 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4151 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4151 8 9, g32p_row03_traceSegment_049_4151_0008, g32p_row03_traceSegment_049_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4176 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4168 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4168 8 9, g32p_row03_traceSegment_049_4168_0008, g32p_row03_traceSegment_049_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 4151 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4151 17 17, g32p_row03_traceSegment_049_4151_0017, g32p_row03_traceSegment_049_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 4117 68 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4117 34 34, g32p_row03_traceSegment_049_4117_0034, g32p_row03_traceSegment_049_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 4050 135 = [0, 0, 4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4050 67 68, g32p_row03_traceSegment_049_4050_0067, g32p_row03_traceSegment_049_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_049 4185 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4201 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4201 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4201 8 9, g32p_row03_traceSegment_049_4201_0008, g32p_row03_traceSegment_049_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_049 4185 33 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4185 16 17, g32p_row03_traceSegment_049_4185_0016, g32p_row03_traceSegment_049_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4218 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4226 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4218 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4218 8 9, g32p_row03_traceSegment_049_4218_0008, g32p_row03_traceSegment_049_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4235 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4235 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4235 8 9, g32p_row03_traceSegment_049_4235_0008, g32p_row03_traceSegment_049_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 4218 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4218 17 17, g32p_row03_traceSegment_049_4218_0017, g32p_row03_traceSegment_049_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_049 4185 67 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4185 33 34, g32p_row03_traceSegment_049_4185_0033, g32p_row03_traceSegment_049_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4252 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4260 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4252 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4252 8 9, g32p_row03_traceSegment_049_4252_0008, g32p_row03_traceSegment_049_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4277 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4269 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4269 8 9, g32p_row03_traceSegment_049_4269_0008, g32p_row03_traceSegment_049_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 4252 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4252 17 17, g32p_row03_traceSegment_049_4252_0017, g32p_row03_traceSegment_049_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4286 8 9, g32p_row03_traceSegment_049_4286_0008, g32p_row03_traceSegment_049_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_049 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_049 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_049_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_049 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4303 8 9, g32p_row03_traceSegment_049_4303_0008, g32p_row03_traceSegment_049_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_049 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4286 17 17, g32p_row03_traceSegment_049_4286_0017, g32p_row03_traceSegment_049_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_049 4252 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4252 34 34, g32p_row03_traceSegment_049_4252_0034, g32p_row03_traceSegment_049_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_049 4185 135 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4185 67 68, g32p_row03_traceSegment_049_4185_0067, g32p_row03_traceSegment_049_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_049_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_049 4050 270 = [0, 0, 16, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 4050 135 135, g32p_row03_traceSegment_049_4050_0135, g32p_row03_traceSegment_049_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_049 3780 540 = [0, 0, 19, 0, 0, 33] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3780 270 270, g32p_row03_traceSegment_049_3780_0270, g32p_row03_traceSegment_049_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_049_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_049 3240 1080 = [0, 0, 62, 0, 0, 39] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 3240 540 540, g32p_row03_traceSegment_049_3240_0540, g32p_row03_traceSegment_049_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_049_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_049 2160 2160 = [0, 0, 89, 0, 0, 105] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 2160 1080 1080, g32p_row03_traceSegment_049_2160_1080, g32p_row03_traceSegment_049_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_049_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_049 0 4320 = [0, 0, 180, 0, 0, 180] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_049 0 2160 2160, g32p_row03_traceSegment_049_0000_2160, g32p_row03_traceSegment_049_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_049 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 49 = [0, 0, 180, 0, 0, 180] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_049_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 35) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 35) (g32p_literalTraceValue 2 35)
      [1, -1, 1] [12960, 12960, 12960] = true := by
  rw [g32p_row03_traceCoefficients_035]
  decide +kernel

theorem g32p_row03_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 37) (g32p_literalTraceValue 2 37)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row03_traceCoefficients_037]
  decide +kernel

theorem g32p_row03_tracePolynomial_038 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 38) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 38) (g32p_literalTraceValue 2 38)
      [1, -1, 1] [4320, 4320] = true := by
  rw [g32p_row03_traceCoefficients_038]
  decide +kernel

theorem g32p_row03_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 40) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 40) (g32p_literalTraceValue 2 40)
      [1, -1, 1] [12960, 12960] = true := by
  rw [g32p_row03_traceCoefficients_040]
  decide +kernel

theorem g32p_row03_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 45) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 45) (g32p_literalTraceValue 2 45)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_045]
  decide +kernel

theorem g32p_row03_tracePolynomial_046 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 46) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 46) (g32p_literalTraceValue 2 46)
      [1, -1, 1] [0, 0, 8640, 8640] = true := by
  rw [g32p_row03_traceCoefficients_046]
  decide +kernel

theorem g32p_row03_tracePolynomial_047 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 47) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 47) (g32p_literalTraceValue 2 47)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_047]
  decide +kernel

theorem g32p_row03_tracePolynomial_049 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 49) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 49) (g32p_literalTraceValue 2 49)
      [1, -1, 1] [0, 0, 4320, 4320] = true := by
  rw [g32p_row03_traceCoefficients_049]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
