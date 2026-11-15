import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_086 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 86 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_086_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 16 8 9, g32p_row03_traceSegment_086_0016_0008, g32p_row03_traceSegment_086_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 0 16 17, g32p_row03_traceSegment_086_0000_0016, g32p_row03_traceSegment_086_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 33 8 9, g32p_row03_traceSegment_086_0033_0008, g32p_row03_traceSegment_086_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 50 8 9, g32p_row03_traceSegment_086_0050_0008, g32p_row03_traceSegment_086_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 33 17 17, g32p_row03_traceSegment_086_0033_0017, g32p_row03_traceSegment_086_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 0 33 34, g32p_row03_traceSegment_086_0000_0033, g32p_row03_traceSegment_086_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 67 8 9, g32p_row03_traceSegment_086_0067_0008, g32p_row03_traceSegment_086_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 84 8 9, g32p_row03_traceSegment_086_0084_0008, g32p_row03_traceSegment_086_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 67 17 17, g32p_row03_traceSegment_086_0067_0017, g32p_row03_traceSegment_086_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 101 8 9, g32p_row03_traceSegment_086_0101_0008, g32p_row03_traceSegment_086_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 118 8 9, g32p_row03_traceSegment_086_0118_0008, g32p_row03_traceSegment_086_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 101 17 17, g32p_row03_traceSegment_086_0101_0017, g32p_row03_traceSegment_086_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 67 34 34, g32p_row03_traceSegment_086_0067_0034, g32p_row03_traceSegment_086_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 0 67 68, g32p_row03_traceSegment_086_0000_0067, g32p_row03_traceSegment_086_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 135 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 151 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 151 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 151 8 9, g32p_row03_traceSegment_086_0151_0008, g32p_row03_traceSegment_086_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 135 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 135 16 17, g32p_row03_traceSegment_086_0135_0016, g32p_row03_traceSegment_086_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 168 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 176 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 168 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 168 8 9, g32p_row03_traceSegment_086_0168_0008, g32p_row03_traceSegment_086_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 185 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 185 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 185 8 9, g32p_row03_traceSegment_086_0185_0008, g32p_row03_traceSegment_086_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 168 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 168 17 17, g32p_row03_traceSegment_086_0168_0017, g32p_row03_traceSegment_086_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 135 67 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 135 33 34, g32p_row03_traceSegment_086_0135_0033, g32p_row03_traceSegment_086_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 202 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 210 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 202 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 202 8 9, g32p_row03_traceSegment_086_0202_0008, g32p_row03_traceSegment_086_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 219 8 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 219 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 219 8 9, g32p_row03_traceSegment_086_0219_0008, g32p_row03_traceSegment_086_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 202 34 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 202 17 17, g32p_row03_traceSegment_086_0202_0017, g32p_row03_traceSegment_086_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 236 8 9, g32p_row03_traceSegment_086_0236_0008, g32p_row03_traceSegment_086_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 253 8 9, g32p_row03_traceSegment_086_0253_0008, g32p_row03_traceSegment_086_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 236 17 17, g32p_row03_traceSegment_086_0236_0017, g32p_row03_traceSegment_086_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 202 68 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 202 34 34, g32p_row03_traceSegment_086_0202_0034, g32p_row03_traceSegment_086_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 135 135 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 135 67 68, g32p_row03_traceSegment_086_0135_0067, g32p_row03_traceSegment_086_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 0 270 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 0 135 135, g32p_row03_traceSegment_086_0000_0135, g32p_row03_traceSegment_086_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 286 8 9, g32p_row03_traceSegment_086_0286_0008, g32p_row03_traceSegment_086_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 270 16 17, g32p_row03_traceSegment_086_0270_0016, g32p_row03_traceSegment_086_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 303 8 9, g32p_row03_traceSegment_086_0303_0008, g32p_row03_traceSegment_086_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 320 8 9, g32p_row03_traceSegment_086_0320_0008, g32p_row03_traceSegment_086_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 303 17 17, g32p_row03_traceSegment_086_0303_0017, g32p_row03_traceSegment_086_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 270 33 34, g32p_row03_traceSegment_086_0270_0033, g32p_row03_traceSegment_086_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 337 8 9, g32p_row03_traceSegment_086_0337_0008, g32p_row03_traceSegment_086_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 354 8 9, g32p_row03_traceSegment_086_0354_0008, g32p_row03_traceSegment_086_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 337 17 17, g32p_row03_traceSegment_086_0337_0017, g32p_row03_traceSegment_086_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 371 8 9, g32p_row03_traceSegment_086_0371_0008, g32p_row03_traceSegment_086_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 388 8 9, g32p_row03_traceSegment_086_0388_0008, g32p_row03_traceSegment_086_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 371 17 17, g32p_row03_traceSegment_086_0371_0017, g32p_row03_traceSegment_086_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 337 34 34, g32p_row03_traceSegment_086_0337_0034, g32p_row03_traceSegment_086_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 270 67 68, g32p_row03_traceSegment_086_0270_0067, g32p_row03_traceSegment_086_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 421 8 9, g32p_row03_traceSegment_086_0421_0008, g32p_row03_traceSegment_086_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 405 16 17, g32p_row03_traceSegment_086_0405_0016, g32p_row03_traceSegment_086_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 438 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 446 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 438 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 438 8 9, g32p_row03_traceSegment_086_0438_0008, g32p_row03_traceSegment_086_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 455 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 463 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 455 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 455 8 9, g32p_row03_traceSegment_086_0455_0008, g32p_row03_traceSegment_086_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 438 34 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 438 17 17, g32p_row03_traceSegment_086_0438_0017, g32p_row03_traceSegment_086_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 405 67 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 405 33 34, g32p_row03_traceSegment_086_0405_0033, g32p_row03_traceSegment_086_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 480 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 472 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 472 8 9, g32p_row03_traceSegment_086_0472_0008, g32p_row03_traceSegment_086_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 489 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 497 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 489 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 489 8 9, g32p_row03_traceSegment_086_0489_0008, g32p_row03_traceSegment_086_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 472 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 472 17 17, g32p_row03_traceSegment_086_0472_0017, g32p_row03_traceSegment_086_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 514 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 506 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 506 8 9, g32p_row03_traceSegment_086_0506_0008, g32p_row03_traceSegment_086_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 523 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 523 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 523 8 9, g32p_row03_traceSegment_086_0523_0008, g32p_row03_traceSegment_086_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 506 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 506 17 17, g32p_row03_traceSegment_086_0506_0017, g32p_row03_traceSegment_086_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 472 68 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 472 34 34, g32p_row03_traceSegment_086_0472_0034, g32p_row03_traceSegment_086_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 405 135 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 405 67 68, g32p_row03_traceSegment_086_0405_0067, g32p_row03_traceSegment_086_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 270 270 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 270 135 135, g32p_row03_traceSegment_086_0270_0135, g32p_row03_traceSegment_086_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_086 0 540 = [0, 0, 0, 0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 0 270 270, g32p_row03_traceSegment_086_0000_0270, g32p_row03_traceSegment_086_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 540 16 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 564 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 556 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 556 8 9, g32p_row03_traceSegment_086_0556_0008, g32p_row03_traceSegment_086_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 540 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 540 16 17, g32p_row03_traceSegment_086_0540_0016, g32p_row03_traceSegment_086_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 581 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 573 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 573 8 9, g32p_row03_traceSegment_086_0573_0008, g32p_row03_traceSegment_086_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 590 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 598 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 590 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 590 8 9, g32p_row03_traceSegment_086_0590_0008, g32p_row03_traceSegment_086_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 573 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 573 17 17, g32p_row03_traceSegment_086_0573_0017, g32p_row03_traceSegment_086_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 540 67 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 540 33 34, g32p_row03_traceSegment_086_0540_0033, g32p_row03_traceSegment_086_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 607 8 9, g32p_row03_traceSegment_086_0607_0008, g32p_row03_traceSegment_086_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 624 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 632 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 624 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 624 8 9, g32p_row03_traceSegment_086_0624_0008, g32p_row03_traceSegment_086_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 607 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 607 17 17, g32p_row03_traceSegment_086_0607_0017, g32p_row03_traceSegment_086_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 649 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 641 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 641 8 9, g32p_row03_traceSegment_086_0641_0008, g32p_row03_traceSegment_086_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 658 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 658 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 658 8 9, g32p_row03_traceSegment_086_0658_0008, g32p_row03_traceSegment_086_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 641 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 641 17 17, g32p_row03_traceSegment_086_0641_0017, g32p_row03_traceSegment_086_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 607 68 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 607 34 34, g32p_row03_traceSegment_086_0607_0034, g32p_row03_traceSegment_086_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 540 135 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 540 67 68, g32p_row03_traceSegment_086_0540_0067, g32p_row03_traceSegment_086_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 675 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 699 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 691 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 691 8 9, g32p_row03_traceSegment_086_0691_0008, g32p_row03_traceSegment_086_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 675 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 675 16 17, g32p_row03_traceSegment_086_0675_0016, g32p_row03_traceSegment_086_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 708 8 9, g32p_row03_traceSegment_086_0708_0008, g32p_row03_traceSegment_086_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 725 8 9, g32p_row03_traceSegment_086_0725_0008, g32p_row03_traceSegment_086_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 708 17 17, g32p_row03_traceSegment_086_0708_0017, g32p_row03_traceSegment_086_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 675 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 675 33 34, g32p_row03_traceSegment_086_0675_0033, g32p_row03_traceSegment_086_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 742 8 9, g32p_row03_traceSegment_086_0742_0008, g32p_row03_traceSegment_086_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 759 8 9, g32p_row03_traceSegment_086_0759_0008, g32p_row03_traceSegment_086_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 742 17 17, g32p_row03_traceSegment_086_0742_0017, g32p_row03_traceSegment_086_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 776 8 9, g32p_row03_traceSegment_086_0776_0008, g32p_row03_traceSegment_086_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 793 8 9, g32p_row03_traceSegment_086_0793_0008, g32p_row03_traceSegment_086_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 776 17 17, g32p_row03_traceSegment_086_0776_0017, g32p_row03_traceSegment_086_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 742 34 34, g32p_row03_traceSegment_086_0742_0034, g32p_row03_traceSegment_086_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 675 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 675 67 68, g32p_row03_traceSegment_086_0675_0067, g32p_row03_traceSegment_086_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 540 270 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 540 135 135, g32p_row03_traceSegment_086_0540_0135, g32p_row03_traceSegment_086_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 826 8 9, g32p_row03_traceSegment_086_0826_0008, g32p_row03_traceSegment_086_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 810 16 17, g32p_row03_traceSegment_086_0810_0016, g32p_row03_traceSegment_086_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 843 8 9, g32p_row03_traceSegment_086_0843_0008, g32p_row03_traceSegment_086_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 860 8 9, g32p_row03_traceSegment_086_0860_0008, g32p_row03_traceSegment_086_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 843 17 17, g32p_row03_traceSegment_086_0843_0017, g32p_row03_traceSegment_086_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 810 33 34, g32p_row03_traceSegment_086_0810_0033, g32p_row03_traceSegment_086_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 877 8 9, g32p_row03_traceSegment_086_0877_0008, g32p_row03_traceSegment_086_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 894 8 9, g32p_row03_traceSegment_086_0894_0008, g32p_row03_traceSegment_086_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 877 17 17, g32p_row03_traceSegment_086_0877_0017, g32p_row03_traceSegment_086_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 911 8 9, g32p_row03_traceSegment_086_0911_0008, g32p_row03_traceSegment_086_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 928 8 9, g32p_row03_traceSegment_086_0928_0008, g32p_row03_traceSegment_086_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 911 17 17, g32p_row03_traceSegment_086_0911_0017, g32p_row03_traceSegment_086_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 877 34 34, g32p_row03_traceSegment_086_0877_0034, g32p_row03_traceSegment_086_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 810 67 68, g32p_row03_traceSegment_086_0810_0067, g32p_row03_traceSegment_086_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 961 8 9, g32p_row03_traceSegment_086_0961_0008, g32p_row03_traceSegment_086_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 945 16 17, g32p_row03_traceSegment_086_0945_0016, g32p_row03_traceSegment_086_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 986 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 978 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 978 8 9, g32p_row03_traceSegment_086_0978_0008, g32p_row03_traceSegment_086_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 995 8 9, g32p_row03_traceSegment_086_0995_0008, g32p_row03_traceSegment_086_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 978 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 978 17 17, g32p_row03_traceSegment_086_0978_0017, g32p_row03_traceSegment_086_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 945 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 945 33 34, g32p_row03_traceSegment_086_0945_0033, g32p_row03_traceSegment_086_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1012 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1012 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1012 8 9, g32p_row03_traceSegment_086_1012_0008, g32p_row03_traceSegment_086_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1029 8 9, g32p_row03_traceSegment_086_1029_0008, g32p_row03_traceSegment_086_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1012 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1012 17 17, g32p_row03_traceSegment_086_1012_0017, g32p_row03_traceSegment_086_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1046 8 9, g32p_row03_traceSegment_086_1046_0008, g32p_row03_traceSegment_086_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1063 8 9, g32p_row03_traceSegment_086_1063_0008, g32p_row03_traceSegment_086_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1046 17 17, g32p_row03_traceSegment_086_1046_0017, g32p_row03_traceSegment_086_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 1012 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1012 34 34, g32p_row03_traceSegment_086_1012_0034, g32p_row03_traceSegment_086_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 945 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 945 67 68, g32p_row03_traceSegment_086_0945_0067, g32p_row03_traceSegment_086_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 810 270 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 810 135 135, g32p_row03_traceSegment_086_0810_0135, g32p_row03_traceSegment_086_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_086 540 540 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 540 270 270, g32p_row03_traceSegment_086_0540_0270, g32p_row03_traceSegment_086_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_086 0 1080 = [0, 0, 0, 0, 0, 37] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 0 540 540, g32p_row03_traceSegment_086_0000_0540, g32p_row03_traceSegment_086_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1096 8 9, g32p_row03_traceSegment_086_1096_0008, g32p_row03_traceSegment_086_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1080 16 17, g32p_row03_traceSegment_086_1080_0016, g32p_row03_traceSegment_086_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1113 8 9, g32p_row03_traceSegment_086_1113_0008, g32p_row03_traceSegment_086_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1130 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1130 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1130 8 9, g32p_row03_traceSegment_086_1130_0008, g32p_row03_traceSegment_086_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1113 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1113 17 17, g32p_row03_traceSegment_086_1113_0017, g32p_row03_traceSegment_086_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 1080 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1080 33 34, g32p_row03_traceSegment_086_1080_0033, g32p_row03_traceSegment_086_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1147 8 9, g32p_row03_traceSegment_086_1147_0008, g32p_row03_traceSegment_086_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1164 8 9, g32p_row03_traceSegment_086_1164_0008, g32p_row03_traceSegment_086_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1147 17 17, g32p_row03_traceSegment_086_1147_0017, g32p_row03_traceSegment_086_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1181 8 9, g32p_row03_traceSegment_086_1181_0008, g32p_row03_traceSegment_086_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1198 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1198 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1198 8 9, g32p_row03_traceSegment_086_1198_0008, g32p_row03_traceSegment_086_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1181 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1181 17 17, g32p_row03_traceSegment_086_1181_0017, g32p_row03_traceSegment_086_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 1147 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1147 34 34, g32p_row03_traceSegment_086_1147_0034, g32p_row03_traceSegment_086_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 1080 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1080 67 68, g32p_row03_traceSegment_086_1080_0067, g32p_row03_traceSegment_086_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1231 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1231 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1231 8 9, g32p_row03_traceSegment_086_1231_0008, g32p_row03_traceSegment_086_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 1215 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1215 16 17, g32p_row03_traceSegment_086_1215_0016, g32p_row03_traceSegment_086_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1248 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1248 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1248 8 9, g32p_row03_traceSegment_086_1248_0008, g32p_row03_traceSegment_086_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1265 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1273 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1265 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1265 8 9, g32p_row03_traceSegment_086_1265_0008, g32p_row03_traceSegment_086_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1248 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1248 17 17, g32p_row03_traceSegment_086_1248_0017, g32p_row03_traceSegment_086_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 1215 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1215 33 34, g32p_row03_traceSegment_086_1215_0033, g32p_row03_traceSegment_086_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1282 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1290 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1282 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1282 8 9, g32p_row03_traceSegment_086_1282_0008, g32p_row03_traceSegment_086_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1299 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1307 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1299 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1299 8 9, g32p_row03_traceSegment_086_1299_0008, g32p_row03_traceSegment_086_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1282 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1282 17 17, g32p_row03_traceSegment_086_1282_0017, g32p_row03_traceSegment_086_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1316 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1316 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1316 8 9, g32p_row03_traceSegment_086_1316_0008, g32p_row03_traceSegment_086_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1341 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1333 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1333 8 9, g32p_row03_traceSegment_086_1333_0008, g32p_row03_traceSegment_086_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1316 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1316 17 17, g32p_row03_traceSegment_086_1316_0017, g32p_row03_traceSegment_086_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 1282 68 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1282 34 34, g32p_row03_traceSegment_086_1282_0034, g32p_row03_traceSegment_086_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 1215 135 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1215 67 68, g32p_row03_traceSegment_086_1215_0067, g32p_row03_traceSegment_086_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 1080 270 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1080 135 135, g32p_row03_traceSegment_086_1080_0135, g32p_row03_traceSegment_086_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1366 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1374 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1366 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1366 8 9, g32p_row03_traceSegment_086_1366_0008, g32p_row03_traceSegment_086_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 1350 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1350 16 17, g32p_row03_traceSegment_086_1350_0016, g32p_row03_traceSegment_086_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1383 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1391 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1383 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1383 8 9, g32p_row03_traceSegment_086_1383_0008, g32p_row03_traceSegment_086_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1400 8 9, g32p_row03_traceSegment_086_1400_0008, g32p_row03_traceSegment_086_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1383 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1383 17 17, g32p_row03_traceSegment_086_1383_0017, g32p_row03_traceSegment_086_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 1350 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1350 33 34, g32p_row03_traceSegment_086_1350_0033, g32p_row03_traceSegment_086_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1417 8 9, g32p_row03_traceSegment_086_1417_0008, g32p_row03_traceSegment_086_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1434 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1434 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1434 8 9, g32p_row03_traceSegment_086_1434_0008, g32p_row03_traceSegment_086_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1417 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1417 17 17, g32p_row03_traceSegment_086_1417_0017, g32p_row03_traceSegment_086_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1451 8 9, g32p_row03_traceSegment_086_1451_0008, g32p_row03_traceSegment_086_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1468 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1468 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1468 8 9, g32p_row03_traceSegment_086_1468_0008, g32p_row03_traceSegment_086_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1451 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1451 17 17, g32p_row03_traceSegment_086_1451_0017, g32p_row03_traceSegment_086_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 1417 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1417 34 34, g32p_row03_traceSegment_086_1417_0034, g32p_row03_traceSegment_086_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 1350 135 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1350 67 68, g32p_row03_traceSegment_086_1350_0067, g32p_row03_traceSegment_086_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1509 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1501 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1501 8 9, g32p_row03_traceSegment_086_1501_0008, g32p_row03_traceSegment_086_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 1485 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1485 16 17, g32p_row03_traceSegment_086_1485_0016, g32p_row03_traceSegment_086_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1518 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1518 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1518 8 9, g32p_row03_traceSegment_086_1518_0008, g32p_row03_traceSegment_086_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1535 8 9, g32p_row03_traceSegment_086_1535_0008, g32p_row03_traceSegment_086_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1518 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1518 17 17, g32p_row03_traceSegment_086_1518_0017, g32p_row03_traceSegment_086_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 1485 67 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1485 33 34, g32p_row03_traceSegment_086_1485_0033, g32p_row03_traceSegment_086_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1552 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1552 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1552 8 9, g32p_row03_traceSegment_086_1552_0008, g32p_row03_traceSegment_086_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1569 8 9, g32p_row03_traceSegment_086_1569_0008, g32p_row03_traceSegment_086_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1552 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1552 17 17, g32p_row03_traceSegment_086_1552_0017, g32p_row03_traceSegment_086_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1594 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1586 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1586 8 9, g32p_row03_traceSegment_086_1586_0008, g32p_row03_traceSegment_086_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1611 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1603 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1603 8 9, g32p_row03_traceSegment_086_1603_0008, g32p_row03_traceSegment_086_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1586 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1586 17 17, g32p_row03_traceSegment_086_1586_0017, g32p_row03_traceSegment_086_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 1552 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1552 34 34, g32p_row03_traceSegment_086_1552_0034, g32p_row03_traceSegment_086_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 1485 135 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1485 67 68, g32p_row03_traceSegment_086_1485_0067, g32p_row03_traceSegment_086_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 1350 270 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1350 135 135, g32p_row03_traceSegment_086_1350_0135, g32p_row03_traceSegment_086_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_086 1080 540 = [0, 0, 0, 0, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1080 270 270, g32p_row03_traceSegment_086_1080_0270, g32p_row03_traceSegment_086_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1636 8 9, g32p_row03_traceSegment_086_1636_0008, g32p_row03_traceSegment_086_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1620 16 17, g32p_row03_traceSegment_086_1620_0016, g32p_row03_traceSegment_086_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1653 8 9, g32p_row03_traceSegment_086_1653_0008, g32p_row03_traceSegment_086_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1670 8 9, g32p_row03_traceSegment_086_1670_0008, g32p_row03_traceSegment_086_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1653 17 17, g32p_row03_traceSegment_086_1653_0017, g32p_row03_traceSegment_086_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1620 33 34, g32p_row03_traceSegment_086_1620_0033, g32p_row03_traceSegment_086_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1687 8 9, g32p_row03_traceSegment_086_1687_0008, g32p_row03_traceSegment_086_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1712 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1704 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1704 8 9, g32p_row03_traceSegment_086_1704_0008, g32p_row03_traceSegment_086_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1687 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1687 17 17, g32p_row03_traceSegment_086_1687_0017, g32p_row03_traceSegment_086_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1729 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1721 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1721 8 9, g32p_row03_traceSegment_086_1721_0008, g32p_row03_traceSegment_086_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1738 8 9, g32p_row03_traceSegment_086_1738_0008, g32p_row03_traceSegment_086_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1721 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1721 17 17, g32p_row03_traceSegment_086_1721_0017, g32p_row03_traceSegment_086_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 1687 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1687 34 34, g32p_row03_traceSegment_086_1687_0034, g32p_row03_traceSegment_086_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 1620 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1620 67 68, g32p_row03_traceSegment_086_1620_0067, g32p_row03_traceSegment_086_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1771 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1771 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1771 8 9, g32p_row03_traceSegment_086_1771_0008, g32p_row03_traceSegment_086_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 1755 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1755 16 17, g32p_row03_traceSegment_086_1755_0016, g32p_row03_traceSegment_086_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1796 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1788 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1788 8 9, g32p_row03_traceSegment_086_1788_0008, g32p_row03_traceSegment_086_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1805 8 9, g32p_row03_traceSegment_086_1805_0008, g32p_row03_traceSegment_086_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1788 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1788 17 17, g32p_row03_traceSegment_086_1788_0017, g32p_row03_traceSegment_086_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 1755 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1755 33 34, g32p_row03_traceSegment_086_1755_0033, g32p_row03_traceSegment_086_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1822 8 9, g32p_row03_traceSegment_086_1822_0008, g32p_row03_traceSegment_086_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1839 8 9, g32p_row03_traceSegment_086_1839_0008, g32p_row03_traceSegment_086_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1822 17 17, g32p_row03_traceSegment_086_1822_0017, g32p_row03_traceSegment_086_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1864 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1856 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1856 8 9, g32p_row03_traceSegment_086_1856_0008, g32p_row03_traceSegment_086_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1873 8 9, g32p_row03_traceSegment_086_1873_0008, g32p_row03_traceSegment_086_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1856 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1856 17 17, g32p_row03_traceSegment_086_1856_0017, g32p_row03_traceSegment_086_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 1822 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1822 34 34, g32p_row03_traceSegment_086_1822_0034, g32p_row03_traceSegment_086_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 1755 135 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1755 67 68, g32p_row03_traceSegment_086_1755_0067, g32p_row03_traceSegment_086_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 1620 270 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1620 135 135, g32p_row03_traceSegment_086_1620_0135, g32p_row03_traceSegment_086_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1906 8 9, g32p_row03_traceSegment_086_1906_0008, g32p_row03_traceSegment_086_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1890 16 17, g32p_row03_traceSegment_086_1890_0016, g32p_row03_traceSegment_086_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1923 8 9, g32p_row03_traceSegment_086_1923_0008, g32p_row03_traceSegment_086_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1940 8 9, g32p_row03_traceSegment_086_1940_0008, g32p_row03_traceSegment_086_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1923 17 17, g32p_row03_traceSegment_086_1923_0017, g32p_row03_traceSegment_086_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1890 33 34, g32p_row03_traceSegment_086_1890_0033, g32p_row03_traceSegment_086_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1957 8 9, g32p_row03_traceSegment_086_1957_0008, g32p_row03_traceSegment_086_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1974 8 9, g32p_row03_traceSegment_086_1974_0008, g32p_row03_traceSegment_086_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1957 17 17, g32p_row03_traceSegment_086_1957_0017, g32p_row03_traceSegment_086_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1991 8 9, g32p_row03_traceSegment_086_1991_0008, g32p_row03_traceSegment_086_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2008 8 9, g32p_row03_traceSegment_086_2008_0008, g32p_row03_traceSegment_086_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1991 17 17, g32p_row03_traceSegment_086_1991_0017, g32p_row03_traceSegment_086_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1957 34 34, g32p_row03_traceSegment_086_1957_0034, g32p_row03_traceSegment_086_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1890 67 68, g32p_row03_traceSegment_086_1890_0067, g32p_row03_traceSegment_086_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2049 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2041 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2041 8 9, g32p_row03_traceSegment_086_2041_0008, g32p_row03_traceSegment_086_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 2025 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2025 16 17, g32p_row03_traceSegment_086_2025_0016, g32p_row03_traceSegment_086_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2066 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2058 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2058 8 9, g32p_row03_traceSegment_086_2058_0008, g32p_row03_traceSegment_086_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2075 8 9, g32p_row03_traceSegment_086_2075_0008, g32p_row03_traceSegment_086_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2058 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2058 17 17, g32p_row03_traceSegment_086_2058_0017, g32p_row03_traceSegment_086_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 2025 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2025 33 34, g32p_row03_traceSegment_086_2025_0033, g32p_row03_traceSegment_086_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2092 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2092 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2092 8 9, g32p_row03_traceSegment_086_2092_0008, g32p_row03_traceSegment_086_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2109 8 9, g32p_row03_traceSegment_086_2109_0008, g32p_row03_traceSegment_086_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2092 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2092 17 17, g32p_row03_traceSegment_086_2092_0017, g32p_row03_traceSegment_086_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2126 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2126 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2126 8 9, g32p_row03_traceSegment_086_2126_0008, g32p_row03_traceSegment_086_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2143 8 9, g32p_row03_traceSegment_086_2143_0008, g32p_row03_traceSegment_086_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2126 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2126 17 17, g32p_row03_traceSegment_086_2126_0017, g32p_row03_traceSegment_086_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 2092 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2092 34 34, g32p_row03_traceSegment_086_2092_0034, g32p_row03_traceSegment_086_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 2025 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2025 67 68, g32p_row03_traceSegment_086_2025_0067, g32p_row03_traceSegment_086_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 1890 270 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1890 135 135, g32p_row03_traceSegment_086_1890_0135, g32p_row03_traceSegment_086_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_086 1620 540 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1620 270 270, g32p_row03_traceSegment_086_1620_0270, g32p_row03_traceSegment_086_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_086_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_086 1080 1080 = [0, 0, 0, 0, 0, 35] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 1080 540 540, g32p_row03_traceSegment_086_1080_0540, g32p_row03_traceSegment_086_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_086 0 2160 = [0, 0, 0, 0, 0, 72] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 0 1080 1080, g32p_row03_traceSegment_086_0000_1080, g32p_row03_traceSegment_086_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 2160 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2176 8 9, g32p_row03_traceSegment_086_2176_0008, g32p_row03_traceSegment_086_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 2160 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2160 16 17, g32p_row03_traceSegment_086_2160_0016, g32p_row03_traceSegment_086_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2193 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2193 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2193 8 9, g32p_row03_traceSegment_086_2193_0008, g32p_row03_traceSegment_086_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2210 8 9, g32p_row03_traceSegment_086_2210_0008, g32p_row03_traceSegment_086_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2193 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2193 17 17, g32p_row03_traceSegment_086_2193_0017, g32p_row03_traceSegment_086_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 2160 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2160 33 34, g32p_row03_traceSegment_086_2160_0033, g32p_row03_traceSegment_086_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2227 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2227 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2227 8 9, g32p_row03_traceSegment_086_2227_0008, g32p_row03_traceSegment_086_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2244 8 9, g32p_row03_traceSegment_086_2244_0008, g32p_row03_traceSegment_086_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2227 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2227 17 17, g32p_row03_traceSegment_086_2227_0017, g32p_row03_traceSegment_086_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2261 8 9, g32p_row03_traceSegment_086_2261_0008, g32p_row03_traceSegment_086_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2278 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2278 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2278 8 9, g32p_row03_traceSegment_086_2278_0008, g32p_row03_traceSegment_086_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2261 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2261 17 17, g32p_row03_traceSegment_086_2261_0017, g32p_row03_traceSegment_086_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 2227 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2227 34 34, g32p_row03_traceSegment_086_2227_0034, g32p_row03_traceSegment_086_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 2160 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2160 67 68, g32p_row03_traceSegment_086_2160_0067, g32p_row03_traceSegment_086_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 2295 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2311 8 9, g32p_row03_traceSegment_086_2311_0008, g32p_row03_traceSegment_086_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 2295 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2295 16 17, g32p_row03_traceSegment_086_2295_0016, g32p_row03_traceSegment_086_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2328 8 9, g32p_row03_traceSegment_086_2328_0008, g32p_row03_traceSegment_086_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2345 8 9, g32p_row03_traceSegment_086_2345_0008, g32p_row03_traceSegment_086_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2328 17 17, g32p_row03_traceSegment_086_2328_0017, g32p_row03_traceSegment_086_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 2295 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2295 33 34, g32p_row03_traceSegment_086_2295_0033, g32p_row03_traceSegment_086_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2362 8 9, g32p_row03_traceSegment_086_2362_0008, g32p_row03_traceSegment_086_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2379 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2379 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2379 8 9, g32p_row03_traceSegment_086_2379_0008, g32p_row03_traceSegment_086_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2362 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2362 17 17, g32p_row03_traceSegment_086_2362_0017, g32p_row03_traceSegment_086_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2404 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2396 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2396 8 9, g32p_row03_traceSegment_086_2396_0008, g32p_row03_traceSegment_086_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2413 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2413 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2413 8 9, g32p_row03_traceSegment_086_2413_0008, g32p_row03_traceSegment_086_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2396 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2396 17 17, g32p_row03_traceSegment_086_2396_0017, g32p_row03_traceSegment_086_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 2362 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2362 34 34, g32p_row03_traceSegment_086_2362_0034, g32p_row03_traceSegment_086_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 2295 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2295 67 68, g32p_row03_traceSegment_086_2295_0067, g32p_row03_traceSegment_086_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 2160 270 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2160 135 135, g32p_row03_traceSegment_086_2160_0135, g32p_row03_traceSegment_086_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2446 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2446 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2446 8 9, g32p_row03_traceSegment_086_2446_0008, g32p_row03_traceSegment_086_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 2430 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2430 16 17, g32p_row03_traceSegment_086_2430_0016, g32p_row03_traceSegment_086_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2463 8 9, g32p_row03_traceSegment_086_2463_0008, g32p_row03_traceSegment_086_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2480 8 9, g32p_row03_traceSegment_086_2480_0008, g32p_row03_traceSegment_086_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2463 17 17, g32p_row03_traceSegment_086_2463_0017, g32p_row03_traceSegment_086_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 2430 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2430 33 34, g32p_row03_traceSegment_086_2430_0033, g32p_row03_traceSegment_086_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2505 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2497 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2497 8 9, g32p_row03_traceSegment_086_2497_0008, g32p_row03_traceSegment_086_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2522 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2514 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2514 8 9, g32p_row03_traceSegment_086_2514_0008, g32p_row03_traceSegment_086_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2497 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2497 17 17, g32p_row03_traceSegment_086_2497_0017, g32p_row03_traceSegment_086_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2531 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2531 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2531 8 9, g32p_row03_traceSegment_086_2531_0008, g32p_row03_traceSegment_086_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2548 8 9, g32p_row03_traceSegment_086_2548_0008, g32p_row03_traceSegment_086_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2531 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2531 17 17, g32p_row03_traceSegment_086_2531_0017, g32p_row03_traceSegment_086_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 2497 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2497 34 34, g32p_row03_traceSegment_086_2497_0034, g32p_row03_traceSegment_086_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 2430 135 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2430 67 68, g32p_row03_traceSegment_086_2430_0067, g32p_row03_traceSegment_086_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2581 8 9, g32p_row03_traceSegment_086_2581_0008, g32p_row03_traceSegment_086_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2565 16 17, g32p_row03_traceSegment_086_2565_0016, g32p_row03_traceSegment_086_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2598 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2598 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2598 8 9, g32p_row03_traceSegment_086_2598_0008, g32p_row03_traceSegment_086_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2615 8 9, g32p_row03_traceSegment_086_2615_0008, g32p_row03_traceSegment_086_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2598 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2598 17 17, g32p_row03_traceSegment_086_2598_0017, g32p_row03_traceSegment_086_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 2565 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2565 33 34, g32p_row03_traceSegment_086_2565_0033, g32p_row03_traceSegment_086_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2640 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2632 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2632 8 9, g32p_row03_traceSegment_086_2632_0008, g32p_row03_traceSegment_086_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2649 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2649 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2649 8 9, g32p_row03_traceSegment_086_2649_0008, g32p_row03_traceSegment_086_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2632 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2632 17 17, g32p_row03_traceSegment_086_2632_0017, g32p_row03_traceSegment_086_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2666 8 9, g32p_row03_traceSegment_086_2666_0008, g32p_row03_traceSegment_086_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2691 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2683 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2683 8 9, g32p_row03_traceSegment_086_2683_0008, g32p_row03_traceSegment_086_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2666 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2666 17 17, g32p_row03_traceSegment_086_2666_0017, g32p_row03_traceSegment_086_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 2632 68 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2632 34 34, g32p_row03_traceSegment_086_2632_0034, g32p_row03_traceSegment_086_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 2565 135 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2565 67 68, g32p_row03_traceSegment_086_2565_0067, g32p_row03_traceSegment_086_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 2430 270 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2430 135 135, g32p_row03_traceSegment_086_2430_0135, g32p_row03_traceSegment_086_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_086 2160 540 = [0, 0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2160 270 270, g32p_row03_traceSegment_086_2160_0270, g32p_row03_traceSegment_086_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 2700 16 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2716 8 9, g32p_row03_traceSegment_086_2716_0008, g32p_row03_traceSegment_086_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 2700 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2700 16 17, g32p_row03_traceSegment_086_2700_0016, g32p_row03_traceSegment_086_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2733 8 9, g32p_row03_traceSegment_086_2733_0008, g32p_row03_traceSegment_086_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2750 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2750 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2750 8 9, g32p_row03_traceSegment_086_2750_0008, g32p_row03_traceSegment_086_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2733 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2733 17 17, g32p_row03_traceSegment_086_2733_0017, g32p_row03_traceSegment_086_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 2700 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2700 33 34, g32p_row03_traceSegment_086_2700_0033, g32p_row03_traceSegment_086_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2767 8 9, g32p_row03_traceSegment_086_2767_0008, g32p_row03_traceSegment_086_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2792 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2784 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2784 8 9, g32p_row03_traceSegment_086_2784_0008, g32p_row03_traceSegment_086_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2767 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2767 17 17, g32p_row03_traceSegment_086_2767_0017, g32p_row03_traceSegment_086_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2801 8 9, g32p_row03_traceSegment_086_2801_0008, g32p_row03_traceSegment_086_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2818 8 9, g32p_row03_traceSegment_086_2818_0008, g32p_row03_traceSegment_086_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2801 17 17, g32p_row03_traceSegment_086_2801_0017, g32p_row03_traceSegment_086_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 2767 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2767 34 34, g32p_row03_traceSegment_086_2767_0034, g32p_row03_traceSegment_086_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 2700 135 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2700 67 68, g32p_row03_traceSegment_086_2700_0067, g32p_row03_traceSegment_086_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 2835 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2851 8 9, g32p_row03_traceSegment_086_2851_0008, g32p_row03_traceSegment_086_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 2835 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2835 16 17, g32p_row03_traceSegment_086_2835_0016, g32p_row03_traceSegment_086_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2868 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2868 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2868 8 9, g32p_row03_traceSegment_086_2868_0008, g32p_row03_traceSegment_086_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2885 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2893 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2885 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2885 8 9, g32p_row03_traceSegment_086_2885_0008, g32p_row03_traceSegment_086_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2868 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2868 17 17, g32p_row03_traceSegment_086_2868_0017, g32p_row03_traceSegment_086_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 2835 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2835 33 34, g32p_row03_traceSegment_086_2835_0033, g32p_row03_traceSegment_086_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2910 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2902 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2902 8 9, g32p_row03_traceSegment_086_2902_0008, g32p_row03_traceSegment_086_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2919 8 9, g32p_row03_traceSegment_086_2919_0008, g32p_row03_traceSegment_086_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2902 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2902 17 17, g32p_row03_traceSegment_086_2902_0017, g32p_row03_traceSegment_086_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2944 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2936 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2936 8 9, g32p_row03_traceSegment_086_2936_0008, g32p_row03_traceSegment_086_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2961 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2953 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2953 8 9, g32p_row03_traceSegment_086_2953_0008, g32p_row03_traceSegment_086_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 2936 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2936 17 17, g32p_row03_traceSegment_086_2936_0017, g32p_row03_traceSegment_086_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 2902 68 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2902 34 34, g32p_row03_traceSegment_086_2902_0034, g32p_row03_traceSegment_086_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 2835 135 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2835 67 68, g32p_row03_traceSegment_086_2835_0067, g32p_row03_traceSegment_086_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 2700 270 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2700 135 135, g32p_row03_traceSegment_086_2700_0135, g32p_row03_traceSegment_086_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2986 8 9, g32p_row03_traceSegment_086_2986_0008, g32p_row03_traceSegment_086_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2970 16 17, g32p_row03_traceSegment_086_2970_0016, g32p_row03_traceSegment_086_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3003 8 9, g32p_row03_traceSegment_086_3003_0008, g32p_row03_traceSegment_086_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3020 8 9, g32p_row03_traceSegment_086_3020_0008, g32p_row03_traceSegment_086_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3003 17 17, g32p_row03_traceSegment_086_3003_0017, g32p_row03_traceSegment_086_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2970 33 34, g32p_row03_traceSegment_086_2970_0033, g32p_row03_traceSegment_086_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3037 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3037 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3037 8 9, g32p_row03_traceSegment_086_3037_0008, g32p_row03_traceSegment_086_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3062 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3054 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3054 8 9, g32p_row03_traceSegment_086_3054_0008, g32p_row03_traceSegment_086_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3037 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3037 17 17, g32p_row03_traceSegment_086_3037_0017, g32p_row03_traceSegment_086_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3071 8 9, g32p_row03_traceSegment_086_3071_0008, g32p_row03_traceSegment_086_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3088 8 9, g32p_row03_traceSegment_086_3088_0008, g32p_row03_traceSegment_086_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3071 17 17, g32p_row03_traceSegment_086_3071_0017, g32p_row03_traceSegment_086_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 3037 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3037 34 34, g32p_row03_traceSegment_086_3037_0034, g32p_row03_traceSegment_086_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 2970 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2970 67 68, g32p_row03_traceSegment_086_2970_0067, g32p_row03_traceSegment_086_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3121 8 9, g32p_row03_traceSegment_086_3121_0008, g32p_row03_traceSegment_086_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3105 16 17, g32p_row03_traceSegment_086_3105_0016, g32p_row03_traceSegment_086_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3138 8 9, g32p_row03_traceSegment_086_3138_0008, g32p_row03_traceSegment_086_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3155 8 9, g32p_row03_traceSegment_086_3155_0008, g32p_row03_traceSegment_086_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3138 17 17, g32p_row03_traceSegment_086_3138_0017, g32p_row03_traceSegment_086_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3105 33 34, g32p_row03_traceSegment_086_3105_0033, g32p_row03_traceSegment_086_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3172 8 9, g32p_row03_traceSegment_086_3172_0008, g32p_row03_traceSegment_086_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3197 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3189 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3189 8 9, g32p_row03_traceSegment_086_3189_0008, g32p_row03_traceSegment_086_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3172 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3172 17 17, g32p_row03_traceSegment_086_3172_0017, g32p_row03_traceSegment_086_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3206 8 9, g32p_row03_traceSegment_086_3206_0008, g32p_row03_traceSegment_086_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3223 8 9, g32p_row03_traceSegment_086_3223_0008, g32p_row03_traceSegment_086_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3206 17 17, g32p_row03_traceSegment_086_3206_0017, g32p_row03_traceSegment_086_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 3172 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3172 34 34, g32p_row03_traceSegment_086_3172_0034, g32p_row03_traceSegment_086_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 3105 135 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3105 67 68, g32p_row03_traceSegment_086_3105_0067, g32p_row03_traceSegment_086_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 2970 270 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2970 135 135, g32p_row03_traceSegment_086_2970_0135, g32p_row03_traceSegment_086_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_086 2700 540 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2700 270 270, g32p_row03_traceSegment_086_2700_0270, g32p_row03_traceSegment_086_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_086 2160 1080 = [0, 0, 0, 0, 0, 35] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2160 540 540, g32p_row03_traceSegment_086_2160_0540, g32p_row03_traceSegment_086_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3256 8 9, g32p_row03_traceSegment_086_3256_0008, g32p_row03_traceSegment_086_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3240 16 17, g32p_row03_traceSegment_086_3240_0016, g32p_row03_traceSegment_086_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3273 8 9, g32p_row03_traceSegment_086_3273_0008, g32p_row03_traceSegment_086_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3290 8 9, g32p_row03_traceSegment_086_3290_0008, g32p_row03_traceSegment_086_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3273 17 17, g32p_row03_traceSegment_086_3273_0017, g32p_row03_traceSegment_086_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3240 33 34, g32p_row03_traceSegment_086_3240_0033, g32p_row03_traceSegment_086_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3307 8 9, g32p_row03_traceSegment_086_3307_0008, g32p_row03_traceSegment_086_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3324 8 9, g32p_row03_traceSegment_086_3324_0008, g32p_row03_traceSegment_086_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3307 17 17, g32p_row03_traceSegment_086_3307_0017, g32p_row03_traceSegment_086_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3341 8 9, g32p_row03_traceSegment_086_3341_0008, g32p_row03_traceSegment_086_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3358 8 9, g32p_row03_traceSegment_086_3358_0008, g32p_row03_traceSegment_086_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3341 17 17, g32p_row03_traceSegment_086_3341_0017, g32p_row03_traceSegment_086_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3307 34 34, g32p_row03_traceSegment_086_3307_0034, g32p_row03_traceSegment_086_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3240 67 68, g32p_row03_traceSegment_086_3240_0067, g32p_row03_traceSegment_086_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3391 8 9, g32p_row03_traceSegment_086_3391_0008, g32p_row03_traceSegment_086_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3375 16 17, g32p_row03_traceSegment_086_3375_0016, g32p_row03_traceSegment_086_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3408 8 9, g32p_row03_traceSegment_086_3408_0008, g32p_row03_traceSegment_086_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3425 8 9, g32p_row03_traceSegment_086_3425_0008, g32p_row03_traceSegment_086_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3408 17 17, g32p_row03_traceSegment_086_3408_0017, g32p_row03_traceSegment_086_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3375 33 34, g32p_row03_traceSegment_086_3375_0033, g32p_row03_traceSegment_086_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3442 8 9, g32p_row03_traceSegment_086_3442_0008, g32p_row03_traceSegment_086_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3459 8 9, g32p_row03_traceSegment_086_3459_0008, g32p_row03_traceSegment_086_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3442 17 17, g32p_row03_traceSegment_086_3442_0017, g32p_row03_traceSegment_086_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3476 8 9, g32p_row03_traceSegment_086_3476_0008, g32p_row03_traceSegment_086_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3493 8 9, g32p_row03_traceSegment_086_3493_0008, g32p_row03_traceSegment_086_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3476 17 17, g32p_row03_traceSegment_086_3476_0017, g32p_row03_traceSegment_086_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3442 34 34, g32p_row03_traceSegment_086_3442_0034, g32p_row03_traceSegment_086_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3375 67 68, g32p_row03_traceSegment_086_3375_0067, g32p_row03_traceSegment_086_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3240 135 135, g32p_row03_traceSegment_086_3240_0135, g32p_row03_traceSegment_086_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3526 8 9, g32p_row03_traceSegment_086_3526_0008, g32p_row03_traceSegment_086_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3510 16 17, g32p_row03_traceSegment_086_3510_0016, g32p_row03_traceSegment_086_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3543 8 9, g32p_row03_traceSegment_086_3543_0008, g32p_row03_traceSegment_086_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3560 8 9, g32p_row03_traceSegment_086_3560_0008, g32p_row03_traceSegment_086_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3543 17 17, g32p_row03_traceSegment_086_3543_0017, g32p_row03_traceSegment_086_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3510 33 34, g32p_row03_traceSegment_086_3510_0033, g32p_row03_traceSegment_086_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3577 8 9, g32p_row03_traceSegment_086_3577_0008, g32p_row03_traceSegment_086_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3594 8 9, g32p_row03_traceSegment_086_3594_0008, g32p_row03_traceSegment_086_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3577 17 17, g32p_row03_traceSegment_086_3577_0017, g32p_row03_traceSegment_086_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3611 8 9, g32p_row03_traceSegment_086_3611_0008, g32p_row03_traceSegment_086_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3628 8 9, g32p_row03_traceSegment_086_3628_0008, g32p_row03_traceSegment_086_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3611 17 17, g32p_row03_traceSegment_086_3611_0017, g32p_row03_traceSegment_086_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3577 34 34, g32p_row03_traceSegment_086_3577_0034, g32p_row03_traceSegment_086_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3510 67 68, g32p_row03_traceSegment_086_3510_0067, g32p_row03_traceSegment_086_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3661 8 9, g32p_row03_traceSegment_086_3661_0008, g32p_row03_traceSegment_086_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3645 16 17, g32p_row03_traceSegment_086_3645_0016, g32p_row03_traceSegment_086_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3678 8 9, g32p_row03_traceSegment_086_3678_0008, g32p_row03_traceSegment_086_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3695 8 9, g32p_row03_traceSegment_086_3695_0008, g32p_row03_traceSegment_086_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3678 17 17, g32p_row03_traceSegment_086_3678_0017, g32p_row03_traceSegment_086_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3645 33 34, g32p_row03_traceSegment_086_3645_0033, g32p_row03_traceSegment_086_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3712 8 9, g32p_row03_traceSegment_086_3712_0008, g32p_row03_traceSegment_086_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3729 8 9, g32p_row03_traceSegment_086_3729_0008, g32p_row03_traceSegment_086_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3712 17 17, g32p_row03_traceSegment_086_3712_0017, g32p_row03_traceSegment_086_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3746 8 9, g32p_row03_traceSegment_086_3746_0008, g32p_row03_traceSegment_086_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3763 8 9, g32p_row03_traceSegment_086_3763_0008, g32p_row03_traceSegment_086_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3746 17 17, g32p_row03_traceSegment_086_3746_0017, g32p_row03_traceSegment_086_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3712 34 34, g32p_row03_traceSegment_086_3712_0034, g32p_row03_traceSegment_086_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3645 67 68, g32p_row03_traceSegment_086_3645_0067, g32p_row03_traceSegment_086_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 3510 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3510 135 135, g32p_row03_traceSegment_086_3510_0135, g32p_row03_traceSegment_086_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_086 3240 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3240 270 270, g32p_row03_traceSegment_086_3240_0270, g32p_row03_traceSegment_086_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3796 8 9, g32p_row03_traceSegment_086_3796_0008, g32p_row03_traceSegment_086_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3780 16 17, g32p_row03_traceSegment_086_3780_0016, g32p_row03_traceSegment_086_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3813 8 9, g32p_row03_traceSegment_086_3813_0008, g32p_row03_traceSegment_086_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3830 8 9, g32p_row03_traceSegment_086_3830_0008, g32p_row03_traceSegment_086_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3813 17 17, g32p_row03_traceSegment_086_3813_0017, g32p_row03_traceSegment_086_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3780 33 34, g32p_row03_traceSegment_086_3780_0033, g32p_row03_traceSegment_086_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3847 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3855 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3847 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3847 8 9, g32p_row03_traceSegment_086_3847_0008, g32p_row03_traceSegment_086_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3864 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3864 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3864 8 9, g32p_row03_traceSegment_086_3864_0008, g32p_row03_traceSegment_086_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3847 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3847 17 17, g32p_row03_traceSegment_086_3847_0017, g32p_row03_traceSegment_086_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3881 8 9, g32p_row03_traceSegment_086_3881_0008, g32p_row03_traceSegment_086_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3906 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3898 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3898 8 9, g32p_row03_traceSegment_086_3898_0008, g32p_row03_traceSegment_086_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3881 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3881 17 17, g32p_row03_traceSegment_086_3881_0017, g32p_row03_traceSegment_086_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 3847 68 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3847 34 34, g32p_row03_traceSegment_086_3847_0034, g32p_row03_traceSegment_086_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 3780 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3780 67 68, g32p_row03_traceSegment_086_3780_0067, g32p_row03_traceSegment_086_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 3915 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3931 8 9, g32p_row03_traceSegment_086_3931_0008, g32p_row03_traceSegment_086_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 3915 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3915 16 17, g32p_row03_traceSegment_086_3915_0016, g32p_row03_traceSegment_086_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3956 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3948 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3948 8 9, g32p_row03_traceSegment_086_3948_0008, g32p_row03_traceSegment_086_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3965 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3965 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3965 8 9, g32p_row03_traceSegment_086_3965_0008, g32p_row03_traceSegment_086_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3948 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3948 17 17, g32p_row03_traceSegment_086_3948_0017, g32p_row03_traceSegment_086_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 3915 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3915 33 34, g32p_row03_traceSegment_086_3915_0033, g32p_row03_traceSegment_086_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3982 8 9, g32p_row03_traceSegment_086_3982_0008, g32p_row03_traceSegment_086_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3999 8 9, g32p_row03_traceSegment_086_3999_0008, g32p_row03_traceSegment_086_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3982 17 17, g32p_row03_traceSegment_086_3982_0017, g32p_row03_traceSegment_086_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4024 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4016 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4016 8 9, g32p_row03_traceSegment_086_4016_0008, g32p_row03_traceSegment_086_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4033 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4033 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4033 8 9, g32p_row03_traceSegment_086_4033_0008, g32p_row03_traceSegment_086_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 4016 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4016 17 17, g32p_row03_traceSegment_086_4016_0017, g32p_row03_traceSegment_086_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 3982 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3982 34 34, g32p_row03_traceSegment_086_3982_0034, g32p_row03_traceSegment_086_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 3915 135 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3915 67 68, g32p_row03_traceSegment_086_3915_0067, g32p_row03_traceSegment_086_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 3780 270 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3780 135 135, g32p_row03_traceSegment_086_3780_0135, g32p_row03_traceSegment_086_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4066 8 9, g32p_row03_traceSegment_086_4066_0008, g32p_row03_traceSegment_086_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4050 16 17, g32p_row03_traceSegment_086_4050_0016, g32p_row03_traceSegment_086_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4083 8 9, g32p_row03_traceSegment_086_4083_0008, g32p_row03_traceSegment_086_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4100 8 9, g32p_row03_traceSegment_086_4100_0008, g32p_row03_traceSegment_086_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4083 17 17, g32p_row03_traceSegment_086_4083_0017, g32p_row03_traceSegment_086_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4050 33 34, g32p_row03_traceSegment_086_4050_0033, g32p_row03_traceSegment_086_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4117 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4117 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4117 8 9, g32p_row03_traceSegment_086_4117_0008, g32p_row03_traceSegment_086_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4134 8 9, g32p_row03_traceSegment_086_4134_0008, g32p_row03_traceSegment_086_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 4117 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4117 17 17, g32p_row03_traceSegment_086_4117_0017, g32p_row03_traceSegment_086_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4159 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4151 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4151 8 9, g32p_row03_traceSegment_086_4151_0008, g32p_row03_traceSegment_086_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4168 8 9, g32p_row03_traceSegment_086_4168_0008, g32p_row03_traceSegment_086_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 4151 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4151 17 17, g32p_row03_traceSegment_086_4151_0017, g32p_row03_traceSegment_086_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 4117 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4117 34 34, g32p_row03_traceSegment_086_4117_0034, g32p_row03_traceSegment_086_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 4050 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4050 67 68, g32p_row03_traceSegment_086_4050_0067, g32p_row03_traceSegment_086_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_086 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4201 8 9, g32p_row03_traceSegment_086_4201_0008, g32p_row03_traceSegment_086_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_086 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4185 16 17, g32p_row03_traceSegment_086_4185_0016, g32p_row03_traceSegment_086_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4218 8 9, g32p_row03_traceSegment_086_4218_0008, g32p_row03_traceSegment_086_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4235 8 9, g32p_row03_traceSegment_086_4235_0008, g32p_row03_traceSegment_086_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4218 17 17, g32p_row03_traceSegment_086_4218_0017, g32p_row03_traceSegment_086_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_086 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4185 33 34, g32p_row03_traceSegment_086_4185_0033, g32p_row03_traceSegment_086_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4252 8 9, g32p_row03_traceSegment_086_4252_0008, g32p_row03_traceSegment_086_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4269 8 9, g32p_row03_traceSegment_086_4269_0008, g32p_row03_traceSegment_086_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4252 17 17, g32p_row03_traceSegment_086_4252_0017, g32p_row03_traceSegment_086_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4286 8 9, g32p_row03_traceSegment_086_4286_0008, g32p_row03_traceSegment_086_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_086 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_086 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_086_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_086 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4303 8 9, g32p_row03_traceSegment_086_4303_0008, g32p_row03_traceSegment_086_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_086 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4286 17 17, g32p_row03_traceSegment_086_4286_0017, g32p_row03_traceSegment_086_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_086 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4252 34 34, g32p_row03_traceSegment_086_4252_0034, g32p_row03_traceSegment_086_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_086 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4185 67 68, g32p_row03_traceSegment_086_4185_0067, g32p_row03_traceSegment_086_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_086_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_086 4050 270 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 4050 135 135, g32p_row03_traceSegment_086_4050_0135, g32p_row03_traceSegment_086_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_086 3780 540 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3780 270 270, g32p_row03_traceSegment_086_3780_0270, g32p_row03_traceSegment_086_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_086_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_086 3240 1080 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 3240 540 540, g32p_row03_traceSegment_086_3240_0540, g32p_row03_traceSegment_086_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_086_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_086 2160 2160 = [0, 0, 0, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 2160 1080 1080, g32p_row03_traceSegment_086_2160_1080, g32p_row03_traceSegment_086_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_086_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_086 0 4320 = [0, 0, 0, 0, 0, 120] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_086 0 2160 2160, g32p_row03_traceSegment_086_0000_2160, g32p_row03_traceSegment_086_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 86 = [0, 0, 0, 0, 0, 120] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_086_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_092 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 92 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_092_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 16 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 24 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 16 17 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 16 8 9, g32p_row03_traceSegment_092_0016_0008, g32p_row03_traceSegment_092_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 0 33 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 0 16 17, g32p_row03_traceSegment_092_0000_0016, g32p_row03_traceSegment_092_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 33 8 9, g32p_row03_traceSegment_092_0033_0008, g32p_row03_traceSegment_092_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 50 8 9, g32p_row03_traceSegment_092_0050_0008, g32p_row03_traceSegment_092_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 33 17 17, g32p_row03_traceSegment_092_0033_0017, g32p_row03_traceSegment_092_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 0 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 0 33 34, g32p_row03_traceSegment_092_0000_0033, g32p_row03_traceSegment_092_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 67 8 9, g32p_row03_traceSegment_092_0067_0008, g32p_row03_traceSegment_092_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 84 8 9, g32p_row03_traceSegment_092_0084_0008, g32p_row03_traceSegment_092_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 67 17 17, g32p_row03_traceSegment_092_0067_0017, g32p_row03_traceSegment_092_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 101 8 9, g32p_row03_traceSegment_092_0101_0008, g32p_row03_traceSegment_092_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 118 8 9, g32p_row03_traceSegment_092_0118_0008, g32p_row03_traceSegment_092_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 101 17 17, g32p_row03_traceSegment_092_0101_0017, g32p_row03_traceSegment_092_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 67 34 34, g32p_row03_traceSegment_092_0067_0034, g32p_row03_traceSegment_092_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 0 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 0 67 68, g32p_row03_traceSegment_092_0000_0067, g32p_row03_traceSegment_092_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 151 8 9, g32p_row03_traceSegment_092_0151_0008, g32p_row03_traceSegment_092_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 135 16 17, g32p_row03_traceSegment_092_0135_0016, g32p_row03_traceSegment_092_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 168 8 9, g32p_row03_traceSegment_092_0168_0008, g32p_row03_traceSegment_092_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 185 8 9, g32p_row03_traceSegment_092_0185_0008, g32p_row03_traceSegment_092_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 168 17 17, g32p_row03_traceSegment_092_0168_0017, g32p_row03_traceSegment_092_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 135 33 34, g32p_row03_traceSegment_092_0135_0033, g32p_row03_traceSegment_092_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 202 8 9, g32p_row03_traceSegment_092_0202_0008, g32p_row03_traceSegment_092_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 219 8 9, g32p_row03_traceSegment_092_0219_0008, g32p_row03_traceSegment_092_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 202 17 17, g32p_row03_traceSegment_092_0202_0017, g32p_row03_traceSegment_092_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 236 8 9, g32p_row03_traceSegment_092_0236_0008, g32p_row03_traceSegment_092_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 253 8 9, g32p_row03_traceSegment_092_0253_0008, g32p_row03_traceSegment_092_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 236 17 17, g32p_row03_traceSegment_092_0236_0017, g32p_row03_traceSegment_092_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 202 34 34, g32p_row03_traceSegment_092_0202_0034, g32p_row03_traceSegment_092_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 135 67 68, g32p_row03_traceSegment_092_0135_0067, g32p_row03_traceSegment_092_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 0 270 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 0 135 135, g32p_row03_traceSegment_092_0000_0135, g32p_row03_traceSegment_092_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 286 8 9, g32p_row03_traceSegment_092_0286_0008, g32p_row03_traceSegment_092_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 270 16 17, g32p_row03_traceSegment_092_0270_0016, g32p_row03_traceSegment_092_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 303 8 9, g32p_row03_traceSegment_092_0303_0008, g32p_row03_traceSegment_092_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 320 8 9, g32p_row03_traceSegment_092_0320_0008, g32p_row03_traceSegment_092_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 303 17 17, g32p_row03_traceSegment_092_0303_0017, g32p_row03_traceSegment_092_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 270 33 34, g32p_row03_traceSegment_092_0270_0033, g32p_row03_traceSegment_092_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 337 8 9, g32p_row03_traceSegment_092_0337_0008, g32p_row03_traceSegment_092_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 354 8 9, g32p_row03_traceSegment_092_0354_0008, g32p_row03_traceSegment_092_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 337 17 17, g32p_row03_traceSegment_092_0337_0017, g32p_row03_traceSegment_092_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 371 8 9, g32p_row03_traceSegment_092_0371_0008, g32p_row03_traceSegment_092_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 388 8 9, g32p_row03_traceSegment_092_0388_0008, g32p_row03_traceSegment_092_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 371 17 17, g32p_row03_traceSegment_092_0371_0017, g32p_row03_traceSegment_092_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 337 34 34, g32p_row03_traceSegment_092_0337_0034, g32p_row03_traceSegment_092_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 270 67 68, g32p_row03_traceSegment_092_0270_0067, g32p_row03_traceSegment_092_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 421 8 9, g32p_row03_traceSegment_092_0421_0008, g32p_row03_traceSegment_092_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 405 16 17, g32p_row03_traceSegment_092_0405_0016, g32p_row03_traceSegment_092_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 438 8 9, g32p_row03_traceSegment_092_0438_0008, g32p_row03_traceSegment_092_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 455 8 9, g32p_row03_traceSegment_092_0455_0008, g32p_row03_traceSegment_092_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 438 17 17, g32p_row03_traceSegment_092_0438_0017, g32p_row03_traceSegment_092_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 405 33 34, g32p_row03_traceSegment_092_0405_0033, g32p_row03_traceSegment_092_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 472 8 9, g32p_row03_traceSegment_092_0472_0008, g32p_row03_traceSegment_092_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 489 8 9, g32p_row03_traceSegment_092_0489_0008, g32p_row03_traceSegment_092_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 472 17 17, g32p_row03_traceSegment_092_0472_0017, g32p_row03_traceSegment_092_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 506 8 9, g32p_row03_traceSegment_092_0506_0008, g32p_row03_traceSegment_092_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 523 8 9, g32p_row03_traceSegment_092_0523_0008, g32p_row03_traceSegment_092_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 506 17 17, g32p_row03_traceSegment_092_0506_0017, g32p_row03_traceSegment_092_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 472 34 34, g32p_row03_traceSegment_092_0472_0034, g32p_row03_traceSegment_092_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 405 67 68, g32p_row03_traceSegment_092_0405_0067, g32p_row03_traceSegment_092_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 270 135 135, g32p_row03_traceSegment_092_0270_0135, g32p_row03_traceSegment_092_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_092 0 540 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 0 270 270, g32p_row03_traceSegment_092_0000_0270, g32p_row03_traceSegment_092_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 556 8 9, g32p_row03_traceSegment_092_0556_0008, g32p_row03_traceSegment_092_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 540 16 17, g32p_row03_traceSegment_092_0540_0016, g32p_row03_traceSegment_092_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 573 8 9, g32p_row03_traceSegment_092_0573_0008, g32p_row03_traceSegment_092_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 590 8 9, g32p_row03_traceSegment_092_0590_0008, g32p_row03_traceSegment_092_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 573 17 17, g32p_row03_traceSegment_092_0573_0017, g32p_row03_traceSegment_092_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 540 33 34, g32p_row03_traceSegment_092_0540_0033, g32p_row03_traceSegment_092_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 607 8 9, g32p_row03_traceSegment_092_0607_0008, g32p_row03_traceSegment_092_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 624 8 9, g32p_row03_traceSegment_092_0624_0008, g32p_row03_traceSegment_092_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 607 17 17, g32p_row03_traceSegment_092_0607_0017, g32p_row03_traceSegment_092_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 641 8 9, g32p_row03_traceSegment_092_0641_0008, g32p_row03_traceSegment_092_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 658 8 9, g32p_row03_traceSegment_092_0658_0008, g32p_row03_traceSegment_092_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 641 17 17, g32p_row03_traceSegment_092_0641_0017, g32p_row03_traceSegment_092_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 607 34 34, g32p_row03_traceSegment_092_0607_0034, g32p_row03_traceSegment_092_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 540 67 68, g32p_row03_traceSegment_092_0540_0067, g32p_row03_traceSegment_092_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 691 8 9, g32p_row03_traceSegment_092_0691_0008, g32p_row03_traceSegment_092_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 675 16 17, g32p_row03_traceSegment_092_0675_0016, g32p_row03_traceSegment_092_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 708 8 9, g32p_row03_traceSegment_092_0708_0008, g32p_row03_traceSegment_092_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 725 8 9, g32p_row03_traceSegment_092_0725_0008, g32p_row03_traceSegment_092_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 708 17 17, g32p_row03_traceSegment_092_0708_0017, g32p_row03_traceSegment_092_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 675 33 34, g32p_row03_traceSegment_092_0675_0033, g32p_row03_traceSegment_092_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 742 8 9, g32p_row03_traceSegment_092_0742_0008, g32p_row03_traceSegment_092_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 759 8 9, g32p_row03_traceSegment_092_0759_0008, g32p_row03_traceSegment_092_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 742 17 17, g32p_row03_traceSegment_092_0742_0017, g32p_row03_traceSegment_092_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 776 8 9, g32p_row03_traceSegment_092_0776_0008, g32p_row03_traceSegment_092_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 793 8 9, g32p_row03_traceSegment_092_0793_0008, g32p_row03_traceSegment_092_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 776 17 17, g32p_row03_traceSegment_092_0776_0017, g32p_row03_traceSegment_092_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 742 34 34, g32p_row03_traceSegment_092_0742_0034, g32p_row03_traceSegment_092_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 675 67 68, g32p_row03_traceSegment_092_0675_0067, g32p_row03_traceSegment_092_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 540 135 135, g32p_row03_traceSegment_092_0540_0135, g32p_row03_traceSegment_092_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 826 8 9, g32p_row03_traceSegment_092_0826_0008, g32p_row03_traceSegment_092_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 810 16 17, g32p_row03_traceSegment_092_0810_0016, g32p_row03_traceSegment_092_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 843 8 9, g32p_row03_traceSegment_092_0843_0008, g32p_row03_traceSegment_092_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 860 8 9, g32p_row03_traceSegment_092_0860_0008, g32p_row03_traceSegment_092_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 843 17 17, g32p_row03_traceSegment_092_0843_0017, g32p_row03_traceSegment_092_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 810 33 34, g32p_row03_traceSegment_092_0810_0033, g32p_row03_traceSegment_092_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 877 8 9, g32p_row03_traceSegment_092_0877_0008, g32p_row03_traceSegment_092_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 894 8 9, g32p_row03_traceSegment_092_0894_0008, g32p_row03_traceSegment_092_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 877 17 17, g32p_row03_traceSegment_092_0877_0017, g32p_row03_traceSegment_092_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 911 8 9, g32p_row03_traceSegment_092_0911_0008, g32p_row03_traceSegment_092_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 928 8 9, g32p_row03_traceSegment_092_0928_0008, g32p_row03_traceSegment_092_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 911 17 17, g32p_row03_traceSegment_092_0911_0017, g32p_row03_traceSegment_092_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 877 34 34, g32p_row03_traceSegment_092_0877_0034, g32p_row03_traceSegment_092_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 810 67 68, g32p_row03_traceSegment_092_0810_0067, g32p_row03_traceSegment_092_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 961 8 9, g32p_row03_traceSegment_092_0961_0008, g32p_row03_traceSegment_092_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 945 16 17, g32p_row03_traceSegment_092_0945_0016, g32p_row03_traceSegment_092_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 978 8 9, g32p_row03_traceSegment_092_0978_0008, g32p_row03_traceSegment_092_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 995 8 9, g32p_row03_traceSegment_092_0995_0008, g32p_row03_traceSegment_092_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 978 17 17, g32p_row03_traceSegment_092_0978_0017, g32p_row03_traceSegment_092_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 945 33 34, g32p_row03_traceSegment_092_0945_0033, g32p_row03_traceSegment_092_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1012 8 9, g32p_row03_traceSegment_092_1012_0008, g32p_row03_traceSegment_092_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1029 8 9, g32p_row03_traceSegment_092_1029_0008, g32p_row03_traceSegment_092_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1012 17 17, g32p_row03_traceSegment_092_1012_0017, g32p_row03_traceSegment_092_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1046 8 9, g32p_row03_traceSegment_092_1046_0008, g32p_row03_traceSegment_092_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1063 8 9, g32p_row03_traceSegment_092_1063_0008, g32p_row03_traceSegment_092_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1046 17 17, g32p_row03_traceSegment_092_1046_0017, g32p_row03_traceSegment_092_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1012 34 34, g32p_row03_traceSegment_092_1012_0034, g32p_row03_traceSegment_092_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 945 67 68, g32p_row03_traceSegment_092_0945_0067, g32p_row03_traceSegment_092_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 810 135 135, g32p_row03_traceSegment_092_0810_0135, g32p_row03_traceSegment_092_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_092 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 540 270 270, g32p_row03_traceSegment_092_0540_0270, g32p_row03_traceSegment_092_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_092 0 1080 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 0 540 540, g32p_row03_traceSegment_092_0000_0540, g32p_row03_traceSegment_092_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1096 8 9, g32p_row03_traceSegment_092_1096_0008, g32p_row03_traceSegment_092_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1080 16 17, g32p_row03_traceSegment_092_1080_0016, g32p_row03_traceSegment_092_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1113 8 9, g32p_row03_traceSegment_092_1113_0008, g32p_row03_traceSegment_092_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1130 8 9, g32p_row03_traceSegment_092_1130_0008, g32p_row03_traceSegment_092_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1113 17 17, g32p_row03_traceSegment_092_1113_0017, g32p_row03_traceSegment_092_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1080 33 34, g32p_row03_traceSegment_092_1080_0033, g32p_row03_traceSegment_092_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1147 8 9, g32p_row03_traceSegment_092_1147_0008, g32p_row03_traceSegment_092_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1164 8 9, g32p_row03_traceSegment_092_1164_0008, g32p_row03_traceSegment_092_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1147 17 17, g32p_row03_traceSegment_092_1147_0017, g32p_row03_traceSegment_092_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1181 8 9, g32p_row03_traceSegment_092_1181_0008, g32p_row03_traceSegment_092_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1198 8 9, g32p_row03_traceSegment_092_1198_0008, g32p_row03_traceSegment_092_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1181 17 17, g32p_row03_traceSegment_092_1181_0017, g32p_row03_traceSegment_092_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1147 34 34, g32p_row03_traceSegment_092_1147_0034, g32p_row03_traceSegment_092_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1080 67 68, g32p_row03_traceSegment_092_1080_0067, g32p_row03_traceSegment_092_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1231 8 9, g32p_row03_traceSegment_092_1231_0008, g32p_row03_traceSegment_092_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1215 16 17, g32p_row03_traceSegment_092_1215_0016, g32p_row03_traceSegment_092_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1248 8 9, g32p_row03_traceSegment_092_1248_0008, g32p_row03_traceSegment_092_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1265 8 9, g32p_row03_traceSegment_092_1265_0008, g32p_row03_traceSegment_092_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1248 17 17, g32p_row03_traceSegment_092_1248_0017, g32p_row03_traceSegment_092_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1215 33 34, g32p_row03_traceSegment_092_1215_0033, g32p_row03_traceSegment_092_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1282 8 9, g32p_row03_traceSegment_092_1282_0008, g32p_row03_traceSegment_092_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1299 8 9, g32p_row03_traceSegment_092_1299_0008, g32p_row03_traceSegment_092_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1282 17 17, g32p_row03_traceSegment_092_1282_0017, g32p_row03_traceSegment_092_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1324 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1316 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1316 8 9, g32p_row03_traceSegment_092_1316_0008, g32p_row03_traceSegment_092_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1333 8 9, g32p_row03_traceSegment_092_1333_0008, g32p_row03_traceSegment_092_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1316 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1316 17 17, g32p_row03_traceSegment_092_1316_0017, g32p_row03_traceSegment_092_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 1282 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1282 34 34, g32p_row03_traceSegment_092_1282_0034, g32p_row03_traceSegment_092_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 1215 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1215 67 68, g32p_row03_traceSegment_092_1215_0067, g32p_row03_traceSegment_092_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 1080 270 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1080 135 135, g32p_row03_traceSegment_092_1080_0135, g32p_row03_traceSegment_092_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1366 8 9, g32p_row03_traceSegment_092_1366_0008, g32p_row03_traceSegment_092_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1350 16 17, g32p_row03_traceSegment_092_1350_0016, g32p_row03_traceSegment_092_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1383 8 9, g32p_row03_traceSegment_092_1383_0008, g32p_row03_traceSegment_092_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1400 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1400 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1400 8 9, g32p_row03_traceSegment_092_1400_0008, g32p_row03_traceSegment_092_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1383 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1383 17 17, g32p_row03_traceSegment_092_1383_0017, g32p_row03_traceSegment_092_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 1350 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1350 33 34, g32p_row03_traceSegment_092_1350_0033, g32p_row03_traceSegment_092_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1417 8 9, g32p_row03_traceSegment_092_1417_0008, g32p_row03_traceSegment_092_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1434 8 9, g32p_row03_traceSegment_092_1434_0008, g32p_row03_traceSegment_092_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1417 17 17, g32p_row03_traceSegment_092_1417_0017, g32p_row03_traceSegment_092_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1451 8 9, g32p_row03_traceSegment_092_1451_0008, g32p_row03_traceSegment_092_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1476 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1468 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1468 8 9, g32p_row03_traceSegment_092_1468_0008, g32p_row03_traceSegment_092_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1451 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1451 17 17, g32p_row03_traceSegment_092_1451_0017, g32p_row03_traceSegment_092_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 1417 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1417 34 34, g32p_row03_traceSegment_092_1417_0034, g32p_row03_traceSegment_092_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 1350 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1350 67 68, g32p_row03_traceSegment_092_1350_0067, g32p_row03_traceSegment_092_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 1485 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1501 8 9, g32p_row03_traceSegment_092_1501_0008, g32p_row03_traceSegment_092_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 1485 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1485 16 17, g32p_row03_traceSegment_092_1485_0016, g32p_row03_traceSegment_092_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1518 8 9, g32p_row03_traceSegment_092_1518_0008, g32p_row03_traceSegment_092_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1535 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1535 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1535 8 9, g32p_row03_traceSegment_092_1535_0008, g32p_row03_traceSegment_092_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1518 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1518 17 17, g32p_row03_traceSegment_092_1518_0017, g32p_row03_traceSegment_092_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 1485 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1485 33 34, g32p_row03_traceSegment_092_1485_0033, g32p_row03_traceSegment_092_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1552 8 9, g32p_row03_traceSegment_092_1552_0008, g32p_row03_traceSegment_092_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1569 8 9, g32p_row03_traceSegment_092_1569_0008, g32p_row03_traceSegment_092_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1552 17 17, g32p_row03_traceSegment_092_1552_0017, g32p_row03_traceSegment_092_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1586 8 9, g32p_row03_traceSegment_092_1586_0008, g32p_row03_traceSegment_092_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1603 8 9, g32p_row03_traceSegment_092_1603_0008, g32p_row03_traceSegment_092_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1586 17 17, g32p_row03_traceSegment_092_1586_0017, g32p_row03_traceSegment_092_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1552 34 34, g32p_row03_traceSegment_092_1552_0034, g32p_row03_traceSegment_092_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 1485 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1485 67 68, g32p_row03_traceSegment_092_1485_0067, g32p_row03_traceSegment_092_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 1350 270 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1350 135 135, g32p_row03_traceSegment_092_1350_0135, g32p_row03_traceSegment_092_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_092 1080 540 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1080 270 270, g32p_row03_traceSegment_092_1080_0270, g32p_row03_traceSegment_092_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1636 8 9, g32p_row03_traceSegment_092_1636_0008, g32p_row03_traceSegment_092_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1620 16 17, g32p_row03_traceSegment_092_1620_0016, g32p_row03_traceSegment_092_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1661 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1653 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1653 8 9, g32p_row03_traceSegment_092_1653_0008, g32p_row03_traceSegment_092_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1670 8 9, g32p_row03_traceSegment_092_1670_0008, g32p_row03_traceSegment_092_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1653 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1653 17 17, g32p_row03_traceSegment_092_1653_0017, g32p_row03_traceSegment_092_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 1620 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1620 33 34, g32p_row03_traceSegment_092_1620_0033, g32p_row03_traceSegment_092_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1687 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1687 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1687 8 9, g32p_row03_traceSegment_092_1687_0008, g32p_row03_traceSegment_092_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1704 8 9, g32p_row03_traceSegment_092_1704_0008, g32p_row03_traceSegment_092_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1687 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1687 17 17, g32p_row03_traceSegment_092_1687_0017, g32p_row03_traceSegment_092_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1721 8 9, g32p_row03_traceSegment_092_1721_0008, g32p_row03_traceSegment_092_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1738 8 9, g32p_row03_traceSegment_092_1738_0008, g32p_row03_traceSegment_092_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1721 17 17, g32p_row03_traceSegment_092_1721_0017, g32p_row03_traceSegment_092_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 1687 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1687 34 34, g32p_row03_traceSegment_092_1687_0034, g32p_row03_traceSegment_092_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 1620 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1620 67 68, g32p_row03_traceSegment_092_1620_0067, g32p_row03_traceSegment_092_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 1755 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1771 8 9, g32p_row03_traceSegment_092_1771_0008, g32p_row03_traceSegment_092_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 1755 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1755 16 17, g32p_row03_traceSegment_092_1755_0016, g32p_row03_traceSegment_092_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1788 8 9, g32p_row03_traceSegment_092_1788_0008, g32p_row03_traceSegment_092_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1805 8 9, g32p_row03_traceSegment_092_1805_0008, g32p_row03_traceSegment_092_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1788 17 17, g32p_row03_traceSegment_092_1788_0017, g32p_row03_traceSegment_092_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 1755 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1755 33 34, g32p_row03_traceSegment_092_1755_0033, g32p_row03_traceSegment_092_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1822 8 9, g32p_row03_traceSegment_092_1822_0008, g32p_row03_traceSegment_092_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1839 8 9, g32p_row03_traceSegment_092_1839_0008, g32p_row03_traceSegment_092_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1822 17 17, g32p_row03_traceSegment_092_1822_0017, g32p_row03_traceSegment_092_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1856 8 9, g32p_row03_traceSegment_092_1856_0008, g32p_row03_traceSegment_092_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1873 8 9, g32p_row03_traceSegment_092_1873_0008, g32p_row03_traceSegment_092_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1856 17 17, g32p_row03_traceSegment_092_1856_0017, g32p_row03_traceSegment_092_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1822 34 34, g32p_row03_traceSegment_092_1822_0034, g32p_row03_traceSegment_092_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 1755 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1755 67 68, g32p_row03_traceSegment_092_1755_0067, g32p_row03_traceSegment_092_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 1620 270 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1620 135 135, g32p_row03_traceSegment_092_1620_0135, g32p_row03_traceSegment_092_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 1890 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1906 8 9, g32p_row03_traceSegment_092_1906_0008, g32p_row03_traceSegment_092_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 1890 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1890 16 17, g32p_row03_traceSegment_092_1890_0016, g32p_row03_traceSegment_092_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1923 8 9, g32p_row03_traceSegment_092_1923_0008, g32p_row03_traceSegment_092_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1940 8 9, g32p_row03_traceSegment_092_1940_0008, g32p_row03_traceSegment_092_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1923 17 17, g32p_row03_traceSegment_092_1923_0017, g32p_row03_traceSegment_092_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 1890 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1890 33 34, g32p_row03_traceSegment_092_1890_0033, g32p_row03_traceSegment_092_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1957 8 9, g32p_row03_traceSegment_092_1957_0008, g32p_row03_traceSegment_092_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1974 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1974 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1974 8 9, g32p_row03_traceSegment_092_1974_0008, g32p_row03_traceSegment_092_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1957 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1957 17 17, g32p_row03_traceSegment_092_1957_0017, g32p_row03_traceSegment_092_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 1999 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 1991 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1991 8 9, g32p_row03_traceSegment_092_1991_0008, g32p_row03_traceSegment_092_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2008 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2008 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2008 8 9, g32p_row03_traceSegment_092_2008_0008, g32p_row03_traceSegment_092_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 1991 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1991 17 17, g32p_row03_traceSegment_092_1991_0017, g32p_row03_traceSegment_092_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 1957 68 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1957 34 34, g32p_row03_traceSegment_092_1957_0034, g32p_row03_traceSegment_092_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 1890 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1890 67 68, g32p_row03_traceSegment_092_1890_0067, g32p_row03_traceSegment_092_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 2025 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2041 8 9, g32p_row03_traceSegment_092_2041_0008, g32p_row03_traceSegment_092_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 2025 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2025 16 17, g32p_row03_traceSegment_092_2025_0016, g32p_row03_traceSegment_092_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2058 8 9, g32p_row03_traceSegment_092_2058_0008, g32p_row03_traceSegment_092_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2075 8 9, g32p_row03_traceSegment_092_2075_0008, g32p_row03_traceSegment_092_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2058 17 17, g32p_row03_traceSegment_092_2058_0017, g32p_row03_traceSegment_092_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 2025 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2025 33 34, g32p_row03_traceSegment_092_2025_0033, g32p_row03_traceSegment_092_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2092 8 9, g32p_row03_traceSegment_092_2092_0008, g32p_row03_traceSegment_092_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2109 8 9, g32p_row03_traceSegment_092_2109_0008, g32p_row03_traceSegment_092_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2092 17 17, g32p_row03_traceSegment_092_2092_0017, g32p_row03_traceSegment_092_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2126 8 9, g32p_row03_traceSegment_092_2126_0008, g32p_row03_traceSegment_092_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2143 8 9, g32p_row03_traceSegment_092_2143_0008, g32p_row03_traceSegment_092_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2126 17 17, g32p_row03_traceSegment_092_2126_0017, g32p_row03_traceSegment_092_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2092 34 34, g32p_row03_traceSegment_092_2092_0034, g32p_row03_traceSegment_092_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 2025 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2025 67 68, g32p_row03_traceSegment_092_2025_0067, g32p_row03_traceSegment_092_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 1890 270 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1890 135 135, g32p_row03_traceSegment_092_1890_0135, g32p_row03_traceSegment_092_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_092 1620 540 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1620 270 270, g32p_row03_traceSegment_092_1620_0270, g32p_row03_traceSegment_092_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_092_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_092 1080 1080 = [0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 1080 540 540, g32p_row03_traceSegment_092_1080_0540, g32p_row03_traceSegment_092_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_092 0 2160 = [0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 0 1080 1080, g32p_row03_traceSegment_092_0000_1080, g32p_row03_traceSegment_092_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2176 8 9, g32p_row03_traceSegment_092_2176_0008, g32p_row03_traceSegment_092_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2160 16 17, g32p_row03_traceSegment_092_2160_0016, g32p_row03_traceSegment_092_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2193 8 9, g32p_row03_traceSegment_092_2193_0008, g32p_row03_traceSegment_092_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2210 8 9, g32p_row03_traceSegment_092_2210_0008, g32p_row03_traceSegment_092_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2193 17 17, g32p_row03_traceSegment_092_2193_0017, g32p_row03_traceSegment_092_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2160 33 34, g32p_row03_traceSegment_092_2160_0033, g32p_row03_traceSegment_092_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2227 8 9, g32p_row03_traceSegment_092_2227_0008, g32p_row03_traceSegment_092_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2244 8 9, g32p_row03_traceSegment_092_2244_0008, g32p_row03_traceSegment_092_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2227 17 17, g32p_row03_traceSegment_092_2227_0017, g32p_row03_traceSegment_092_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2261 8 9, g32p_row03_traceSegment_092_2261_0008, g32p_row03_traceSegment_092_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2278 8 9, g32p_row03_traceSegment_092_2278_0008, g32p_row03_traceSegment_092_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2261 17 17, g32p_row03_traceSegment_092_2261_0017, g32p_row03_traceSegment_092_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2227 34 34, g32p_row03_traceSegment_092_2227_0034, g32p_row03_traceSegment_092_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2160 67 68, g32p_row03_traceSegment_092_2160_0067, g32p_row03_traceSegment_092_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2311 8 9, g32p_row03_traceSegment_092_2311_0008, g32p_row03_traceSegment_092_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2295 16 17, g32p_row03_traceSegment_092_2295_0016, g32p_row03_traceSegment_092_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2328 8 9, g32p_row03_traceSegment_092_2328_0008, g32p_row03_traceSegment_092_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2345 8 9, g32p_row03_traceSegment_092_2345_0008, g32p_row03_traceSegment_092_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2328 17 17, g32p_row03_traceSegment_092_2328_0017, g32p_row03_traceSegment_092_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2295 33 34, g32p_row03_traceSegment_092_2295_0033, g32p_row03_traceSegment_092_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2362 8 9, g32p_row03_traceSegment_092_2362_0008, g32p_row03_traceSegment_092_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2379 8 9, g32p_row03_traceSegment_092_2379_0008, g32p_row03_traceSegment_092_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2362 17 17, g32p_row03_traceSegment_092_2362_0017, g32p_row03_traceSegment_092_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2396 8 9, g32p_row03_traceSegment_092_2396_0008, g32p_row03_traceSegment_092_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2413 8 9, g32p_row03_traceSegment_092_2413_0008, g32p_row03_traceSegment_092_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2396 17 17, g32p_row03_traceSegment_092_2396_0017, g32p_row03_traceSegment_092_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2362 34 34, g32p_row03_traceSegment_092_2362_0034, g32p_row03_traceSegment_092_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2295 67 68, g32p_row03_traceSegment_092_2295_0067, g32p_row03_traceSegment_092_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 2160 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2160 135 135, g32p_row03_traceSegment_092_2160_0135, g32p_row03_traceSegment_092_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2446 8 9, g32p_row03_traceSegment_092_2446_0008, g32p_row03_traceSegment_092_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2430 16 17, g32p_row03_traceSegment_092_2430_0016, g32p_row03_traceSegment_092_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2463 8 9, g32p_row03_traceSegment_092_2463_0008, g32p_row03_traceSegment_092_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2480 8 9, g32p_row03_traceSegment_092_2480_0008, g32p_row03_traceSegment_092_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2463 17 17, g32p_row03_traceSegment_092_2463_0017, g32p_row03_traceSegment_092_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2430 33 34, g32p_row03_traceSegment_092_2430_0033, g32p_row03_traceSegment_092_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2497 8 9, g32p_row03_traceSegment_092_2497_0008, g32p_row03_traceSegment_092_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2514 8 9, g32p_row03_traceSegment_092_2514_0008, g32p_row03_traceSegment_092_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2497 17 17, g32p_row03_traceSegment_092_2497_0017, g32p_row03_traceSegment_092_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2531 8 9, g32p_row03_traceSegment_092_2531_0008, g32p_row03_traceSegment_092_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2548 8 9, g32p_row03_traceSegment_092_2548_0008, g32p_row03_traceSegment_092_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2531 17 17, g32p_row03_traceSegment_092_2531_0017, g32p_row03_traceSegment_092_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2497 34 34, g32p_row03_traceSegment_092_2497_0034, g32p_row03_traceSegment_092_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2430 67 68, g32p_row03_traceSegment_092_2430_0067, g32p_row03_traceSegment_092_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2581 8 9, g32p_row03_traceSegment_092_2581_0008, g32p_row03_traceSegment_092_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2565 16 17, g32p_row03_traceSegment_092_2565_0016, g32p_row03_traceSegment_092_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2598 8 9, g32p_row03_traceSegment_092_2598_0008, g32p_row03_traceSegment_092_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2615 8 9, g32p_row03_traceSegment_092_2615_0008, g32p_row03_traceSegment_092_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2598 17 17, g32p_row03_traceSegment_092_2598_0017, g32p_row03_traceSegment_092_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2565 33 34, g32p_row03_traceSegment_092_2565_0033, g32p_row03_traceSegment_092_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2632 8 9, g32p_row03_traceSegment_092_2632_0008, g32p_row03_traceSegment_092_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2649 8 9, g32p_row03_traceSegment_092_2649_0008, g32p_row03_traceSegment_092_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2632 17 17, g32p_row03_traceSegment_092_2632_0017, g32p_row03_traceSegment_092_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2666 8 9, g32p_row03_traceSegment_092_2666_0008, g32p_row03_traceSegment_092_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2683 8 9, g32p_row03_traceSegment_092_2683_0008, g32p_row03_traceSegment_092_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2666 17 17, g32p_row03_traceSegment_092_2666_0017, g32p_row03_traceSegment_092_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2632 34 34, g32p_row03_traceSegment_092_2632_0034, g32p_row03_traceSegment_092_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2565 67 68, g32p_row03_traceSegment_092_2565_0067, g32p_row03_traceSegment_092_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2430 135 135, g32p_row03_traceSegment_092_2430_0135, g32p_row03_traceSegment_092_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_092 2160 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2160 270 270, g32p_row03_traceSegment_092_2160_0270, g32p_row03_traceSegment_092_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2716 8 9, g32p_row03_traceSegment_092_2716_0008, g32p_row03_traceSegment_092_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2700 16 17, g32p_row03_traceSegment_092_2700_0016, g32p_row03_traceSegment_092_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2741 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2733 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2733 8 9, g32p_row03_traceSegment_092_2733_0008, g32p_row03_traceSegment_092_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2750 8 9, g32p_row03_traceSegment_092_2750_0008, g32p_row03_traceSegment_092_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2733 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2733 17 17, g32p_row03_traceSegment_092_2733_0017, g32p_row03_traceSegment_092_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 2700 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2700 33 34, g32p_row03_traceSegment_092_2700_0033, g32p_row03_traceSegment_092_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2767 8 9, g32p_row03_traceSegment_092_2767_0008, g32p_row03_traceSegment_092_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2784 8 9, g32p_row03_traceSegment_092_2784_0008, g32p_row03_traceSegment_092_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2767 17 17, g32p_row03_traceSegment_092_2767_0017, g32p_row03_traceSegment_092_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2801 8 9, g32p_row03_traceSegment_092_2801_0008, g32p_row03_traceSegment_092_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2818 8 9, g32p_row03_traceSegment_092_2818_0008, g32p_row03_traceSegment_092_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2801 17 17, g32p_row03_traceSegment_092_2801_0017, g32p_row03_traceSegment_092_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2767 34 34, g32p_row03_traceSegment_092_2767_0034, g32p_row03_traceSegment_092_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 2700 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2700 67 68, g32p_row03_traceSegment_092_2700_0067, g32p_row03_traceSegment_092_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2859 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2851 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2851 8 9, g32p_row03_traceSegment_092_2851_0008, g32p_row03_traceSegment_092_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 2835 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2835 16 17, g32p_row03_traceSegment_092_2835_0016, g32p_row03_traceSegment_092_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2868 8 9, g32p_row03_traceSegment_092_2868_0008, g32p_row03_traceSegment_092_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2885 8 9, g32p_row03_traceSegment_092_2885_0008, g32p_row03_traceSegment_092_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2868 17 17, g32p_row03_traceSegment_092_2868_0017, g32p_row03_traceSegment_092_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 2835 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2835 33 34, g32p_row03_traceSegment_092_2835_0033, g32p_row03_traceSegment_092_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2902 8 9, g32p_row03_traceSegment_092_2902_0008, g32p_row03_traceSegment_092_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2919 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2919 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2919 8 9, g32p_row03_traceSegment_092_2919_0008, g32p_row03_traceSegment_092_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2902 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2902 17 17, g32p_row03_traceSegment_092_2902_0017, g32p_row03_traceSegment_092_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2936 8 9, g32p_row03_traceSegment_092_2936_0008, g32p_row03_traceSegment_092_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2953 8 9, g32p_row03_traceSegment_092_2953_0008, g32p_row03_traceSegment_092_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2936 17 17, g32p_row03_traceSegment_092_2936_0017, g32p_row03_traceSegment_092_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 2902 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2902 34 34, g32p_row03_traceSegment_092_2902_0034, g32p_row03_traceSegment_092_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 2835 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2835 67 68, g32p_row03_traceSegment_092_2835_0067, g32p_row03_traceSegment_092_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 2700 270 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2700 135 135, g32p_row03_traceSegment_092_2700_0135, g32p_row03_traceSegment_092_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2986 8 9, g32p_row03_traceSegment_092_2986_0008, g32p_row03_traceSegment_092_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2970 16 17, g32p_row03_traceSegment_092_2970_0016, g32p_row03_traceSegment_092_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3003 8 9, g32p_row03_traceSegment_092_3003_0008, g32p_row03_traceSegment_092_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3028 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3020 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3020 8 9, g32p_row03_traceSegment_092_3020_0008, g32p_row03_traceSegment_092_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3003 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3003 17 17, g32p_row03_traceSegment_092_3003_0017, g32p_row03_traceSegment_092_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 2970 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2970 33 34, g32p_row03_traceSegment_092_2970_0033, g32p_row03_traceSegment_092_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3037 8 9, g32p_row03_traceSegment_092_3037_0008, g32p_row03_traceSegment_092_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3054 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3054 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3054 8 9, g32p_row03_traceSegment_092_3054_0008, g32p_row03_traceSegment_092_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3037 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3037 17 17, g32p_row03_traceSegment_092_3037_0017, g32p_row03_traceSegment_092_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3071 8 9, g32p_row03_traceSegment_092_3071_0008, g32p_row03_traceSegment_092_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3088 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3088 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3088 8 9, g32p_row03_traceSegment_092_3088_0008, g32p_row03_traceSegment_092_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3071 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3071 17 17, g32p_row03_traceSegment_092_3071_0017, g32p_row03_traceSegment_092_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 3037 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3037 34 34, g32p_row03_traceSegment_092_3037_0034, g32p_row03_traceSegment_092_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 2970 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2970 67 68, g32p_row03_traceSegment_092_2970_0067, g32p_row03_traceSegment_092_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 3105 16 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3121 8 9, g32p_row03_traceSegment_092_3121_0008, g32p_row03_traceSegment_092_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 3105 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3105 16 17, g32p_row03_traceSegment_092_3105_0016, g32p_row03_traceSegment_092_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3138 8 9, g32p_row03_traceSegment_092_3138_0008, g32p_row03_traceSegment_092_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3163 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3155 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3155 8 9, g32p_row03_traceSegment_092_3155_0008, g32p_row03_traceSegment_092_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3138 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3138 17 17, g32p_row03_traceSegment_092_3138_0017, g32p_row03_traceSegment_092_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 3105 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3105 33 34, g32p_row03_traceSegment_092_3105_0033, g32p_row03_traceSegment_092_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3172 8 9, g32p_row03_traceSegment_092_3172_0008, g32p_row03_traceSegment_092_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3189 8 9, g32p_row03_traceSegment_092_3189_0008, g32p_row03_traceSegment_092_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3172 17 17, g32p_row03_traceSegment_092_3172_0017, g32p_row03_traceSegment_092_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3206 8 9, g32p_row03_traceSegment_092_3206_0008, g32p_row03_traceSegment_092_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3223 8 9, g32p_row03_traceSegment_092_3223_0008, g32p_row03_traceSegment_092_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3206 17 17, g32p_row03_traceSegment_092_3206_0017, g32p_row03_traceSegment_092_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3172 34 34, g32p_row03_traceSegment_092_3172_0034, g32p_row03_traceSegment_092_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 3105 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3105 67 68, g32p_row03_traceSegment_092_3105_0067, g32p_row03_traceSegment_092_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 2970 270 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2970 135 135, g32p_row03_traceSegment_092_2970_0135, g32p_row03_traceSegment_092_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_092 2700 540 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2700 270 270, g32p_row03_traceSegment_092_2700_0270, g32p_row03_traceSegment_092_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_092 2160 1080 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2160 540 540, g32p_row03_traceSegment_092_2160_0540, g32p_row03_traceSegment_092_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3256 8 9, g32p_row03_traceSegment_092_3256_0008, g32p_row03_traceSegment_092_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3240 16 17, g32p_row03_traceSegment_092_3240_0016, g32p_row03_traceSegment_092_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3273 8 9, g32p_row03_traceSegment_092_3273_0008, g32p_row03_traceSegment_092_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3290 8 9, g32p_row03_traceSegment_092_3290_0008, g32p_row03_traceSegment_092_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3273 17 17, g32p_row03_traceSegment_092_3273_0017, g32p_row03_traceSegment_092_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3240 33 34, g32p_row03_traceSegment_092_3240_0033, g32p_row03_traceSegment_092_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3307 8 9, g32p_row03_traceSegment_092_3307_0008, g32p_row03_traceSegment_092_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3324 8 9, g32p_row03_traceSegment_092_3324_0008, g32p_row03_traceSegment_092_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3307 17 17, g32p_row03_traceSegment_092_3307_0017, g32p_row03_traceSegment_092_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3341 8 9, g32p_row03_traceSegment_092_3341_0008, g32p_row03_traceSegment_092_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3358 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3366 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3358 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3358 8 9, g32p_row03_traceSegment_092_3358_0008, g32p_row03_traceSegment_092_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3341 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3341 17 17, g32p_row03_traceSegment_092_3341_0017, g32p_row03_traceSegment_092_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 3307 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3307 34 34, g32p_row03_traceSegment_092_3307_0034, g32p_row03_traceSegment_092_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 3240 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3240 67 68, g32p_row03_traceSegment_092_3240_0067, g32p_row03_traceSegment_092_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3399 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3391 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3391 8 9, g32p_row03_traceSegment_092_3391_0008, g32p_row03_traceSegment_092_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 3375 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3375 16 17, g32p_row03_traceSegment_092_3375_0016, g32p_row03_traceSegment_092_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3408 8 9, g32p_row03_traceSegment_092_3408_0008, g32p_row03_traceSegment_092_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3425 8 9, g32p_row03_traceSegment_092_3425_0008, g32p_row03_traceSegment_092_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3408 17 17, g32p_row03_traceSegment_092_3408_0017, g32p_row03_traceSegment_092_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 3375 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3375 33 34, g32p_row03_traceSegment_092_3375_0033, g32p_row03_traceSegment_092_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3450 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3442 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3442 8 9, g32p_row03_traceSegment_092_3442_0008, g32p_row03_traceSegment_092_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3459 8 9, g32p_row03_traceSegment_092_3459_0008, g32p_row03_traceSegment_092_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3442 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3442 17 17, g32p_row03_traceSegment_092_3442_0017, g32p_row03_traceSegment_092_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3476 8 9, g32p_row03_traceSegment_092_3476_0008, g32p_row03_traceSegment_092_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3493 8 9, g32p_row03_traceSegment_092_3493_0008, g32p_row03_traceSegment_092_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3476 17 17, g32p_row03_traceSegment_092_3476_0017, g32p_row03_traceSegment_092_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 3442 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3442 34 34, g32p_row03_traceSegment_092_3442_0034, g32p_row03_traceSegment_092_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 3375 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3375 67 68, g32p_row03_traceSegment_092_3375_0067, g32p_row03_traceSegment_092_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 3240 270 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3240 135 135, g32p_row03_traceSegment_092_3240_0135, g32p_row03_traceSegment_092_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 3510 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3526 8 9, g32p_row03_traceSegment_092_3526_0008, g32p_row03_traceSegment_092_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 3510 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3510 16 17, g32p_row03_traceSegment_092_3510_0016, g32p_row03_traceSegment_092_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3543 8 9, g32p_row03_traceSegment_092_3543_0008, g32p_row03_traceSegment_092_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3560 8 9, g32p_row03_traceSegment_092_3560_0008, g32p_row03_traceSegment_092_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3543 17 17, g32p_row03_traceSegment_092_3543_0017, g32p_row03_traceSegment_092_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 3510 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3510 33 34, g32p_row03_traceSegment_092_3510_0033, g32p_row03_traceSegment_092_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3577 8 9, g32p_row03_traceSegment_092_3577_0008, g32p_row03_traceSegment_092_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3594 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3594 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3594 8 9, g32p_row03_traceSegment_092_3594_0008, g32p_row03_traceSegment_092_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3577 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3577 17 17, g32p_row03_traceSegment_092_3577_0017, g32p_row03_traceSegment_092_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3611 8 9, g32p_row03_traceSegment_092_3611_0008, g32p_row03_traceSegment_092_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3636 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3628 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3628 8 9, g32p_row03_traceSegment_092_3628_0008, g32p_row03_traceSegment_092_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3611 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3611 17 17, g32p_row03_traceSegment_092_3611_0017, g32p_row03_traceSegment_092_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 3577 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3577 34 34, g32p_row03_traceSegment_092_3577_0034, g32p_row03_traceSegment_092_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 3510 135 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3510 67 68, g32p_row03_traceSegment_092_3510_0067, g32p_row03_traceSegment_092_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3661 8 9, g32p_row03_traceSegment_092_3661_0008, g32p_row03_traceSegment_092_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3645 16 17, g32p_row03_traceSegment_092_3645_0016, g32p_row03_traceSegment_092_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3678 8 9, g32p_row03_traceSegment_092_3678_0008, g32p_row03_traceSegment_092_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3695 8 9, g32p_row03_traceSegment_092_3695_0008, g32p_row03_traceSegment_092_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3678 17 17, g32p_row03_traceSegment_092_3678_0017, g32p_row03_traceSegment_092_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3645 33 34, g32p_row03_traceSegment_092_3645_0033, g32p_row03_traceSegment_092_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3720 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3712 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3712 8 9, g32p_row03_traceSegment_092_3712_0008, g32p_row03_traceSegment_092_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3729 8 9, g32p_row03_traceSegment_092_3729_0008, g32p_row03_traceSegment_092_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3712 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3712 17 17, g32p_row03_traceSegment_092_3712_0017, g32p_row03_traceSegment_092_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3746 8 9, g32p_row03_traceSegment_092_3746_0008, g32p_row03_traceSegment_092_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3763 8 9, g32p_row03_traceSegment_092_3763_0008, g32p_row03_traceSegment_092_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3746 17 17, g32p_row03_traceSegment_092_3746_0017, g32p_row03_traceSegment_092_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 3712 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3712 34 34, g32p_row03_traceSegment_092_3712_0034, g32p_row03_traceSegment_092_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 3645 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3645 67 68, g32p_row03_traceSegment_092_3645_0067, g32p_row03_traceSegment_092_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 3510 270 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3510 135 135, g32p_row03_traceSegment_092_3510_0135, g32p_row03_traceSegment_092_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_092 3240 540 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3240 270 270, g32p_row03_traceSegment_092_3240_0270, g32p_row03_traceSegment_092_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3796 8 9, g32p_row03_traceSegment_092_3796_0008, g32p_row03_traceSegment_092_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3780 16 17, g32p_row03_traceSegment_092_3780_0016, g32p_row03_traceSegment_092_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3813 8 9, g32p_row03_traceSegment_092_3813_0008, g32p_row03_traceSegment_092_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3830 8 9, g32p_row03_traceSegment_092_3830_0008, g32p_row03_traceSegment_092_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3813 17 17, g32p_row03_traceSegment_092_3813_0017, g32p_row03_traceSegment_092_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3780 33 34, g32p_row03_traceSegment_092_3780_0033, g32p_row03_traceSegment_092_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3847 8 9, g32p_row03_traceSegment_092_3847_0008, g32p_row03_traceSegment_092_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3864 8 9, g32p_row03_traceSegment_092_3864_0008, g32p_row03_traceSegment_092_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3847 17 17, g32p_row03_traceSegment_092_3847_0017, g32p_row03_traceSegment_092_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3881 8 9, g32p_row03_traceSegment_092_3881_0008, g32p_row03_traceSegment_092_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3898 8 9, g32p_row03_traceSegment_092_3898_0008, g32p_row03_traceSegment_092_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3881 17 17, g32p_row03_traceSegment_092_3881_0017, g32p_row03_traceSegment_092_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3847 34 34, g32p_row03_traceSegment_092_3847_0034, g32p_row03_traceSegment_092_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3780 67 68, g32p_row03_traceSegment_092_3780_0067, g32p_row03_traceSegment_092_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3939 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3931 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3931 8 9, g32p_row03_traceSegment_092_3931_0008, g32p_row03_traceSegment_092_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 3915 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3915 16 17, g32p_row03_traceSegment_092_3915_0016, g32p_row03_traceSegment_092_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3948 8 9, g32p_row03_traceSegment_092_3948_0008, g32p_row03_traceSegment_092_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3965 8 9, g32p_row03_traceSegment_092_3965_0008, g32p_row03_traceSegment_092_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3948 17 17, g32p_row03_traceSegment_092_3948_0017, g32p_row03_traceSegment_092_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 3915 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3915 33 34, g32p_row03_traceSegment_092_3915_0033, g32p_row03_traceSegment_092_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3982 8 9, g32p_row03_traceSegment_092_3982_0008, g32p_row03_traceSegment_092_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3999 8 9, g32p_row03_traceSegment_092_3999_0008, g32p_row03_traceSegment_092_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3982 17 17, g32p_row03_traceSegment_092_3982_0017, g32p_row03_traceSegment_092_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4024 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4016 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4016 8 9, g32p_row03_traceSegment_092_4016_0008, g32p_row03_traceSegment_092_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4033 8 9, g32p_row03_traceSegment_092_4033_0008, g32p_row03_traceSegment_092_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 4016 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4016 17 17, g32p_row03_traceSegment_092_4016_0017, g32p_row03_traceSegment_092_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 3982 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3982 34 34, g32p_row03_traceSegment_092_3982_0034, g32p_row03_traceSegment_092_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 3915 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3915 67 68, g32p_row03_traceSegment_092_3915_0067, g32p_row03_traceSegment_092_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 3780 270 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3780 135 135, g32p_row03_traceSegment_092_3780_0135, g32p_row03_traceSegment_092_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4066 8 9, g32p_row03_traceSegment_092_4066_0008, g32p_row03_traceSegment_092_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4050 16 17, g32p_row03_traceSegment_092_4050_0016, g32p_row03_traceSegment_092_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4083 8 9, g32p_row03_traceSegment_092_4083_0008, g32p_row03_traceSegment_092_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4100 8 9, g32p_row03_traceSegment_092_4100_0008, g32p_row03_traceSegment_092_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4083 17 17, g32p_row03_traceSegment_092_4083_0017, g32p_row03_traceSegment_092_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4050 33 34, g32p_row03_traceSegment_092_4050_0033, g32p_row03_traceSegment_092_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4117 8 9, g32p_row03_traceSegment_092_4117_0008, g32p_row03_traceSegment_092_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4134 8 9, g32p_row03_traceSegment_092_4134_0008, g32p_row03_traceSegment_092_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4117 17 17, g32p_row03_traceSegment_092_4117_0017, g32p_row03_traceSegment_092_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4151 8 9, g32p_row03_traceSegment_092_4151_0008, g32p_row03_traceSegment_092_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4168 8 9, g32p_row03_traceSegment_092_4168_0008, g32p_row03_traceSegment_092_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4151 17 17, g32p_row03_traceSegment_092_4151_0017, g32p_row03_traceSegment_092_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4117 34 34, g32p_row03_traceSegment_092_4117_0034, g32p_row03_traceSegment_092_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4050 67 68, g32p_row03_traceSegment_092_4050_0067, g32p_row03_traceSegment_092_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_092 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4201 8 9, g32p_row03_traceSegment_092_4201_0008, g32p_row03_traceSegment_092_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_092 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4185 16 17, g32p_row03_traceSegment_092_4185_0016, g32p_row03_traceSegment_092_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4218 8 9, g32p_row03_traceSegment_092_4218_0008, g32p_row03_traceSegment_092_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4235 8 9, g32p_row03_traceSegment_092_4235_0008, g32p_row03_traceSegment_092_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4218 17 17, g32p_row03_traceSegment_092_4218_0017, g32p_row03_traceSegment_092_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_092 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4185 33 34, g32p_row03_traceSegment_092_4185_0033, g32p_row03_traceSegment_092_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4252 8 9, g32p_row03_traceSegment_092_4252_0008, g32p_row03_traceSegment_092_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4269 8 9, g32p_row03_traceSegment_092_4269_0008, g32p_row03_traceSegment_092_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4252 17 17, g32p_row03_traceSegment_092_4252_0017, g32p_row03_traceSegment_092_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4286 8 9, g32p_row03_traceSegment_092_4286_0008, g32p_row03_traceSegment_092_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_092 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_092 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_092_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_092 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4303 8 9, g32p_row03_traceSegment_092_4303_0008, g32p_row03_traceSegment_092_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_092 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4286 17 17, g32p_row03_traceSegment_092_4286_0017, g32p_row03_traceSegment_092_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_092 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4252 34 34, g32p_row03_traceSegment_092_4252_0034, g32p_row03_traceSegment_092_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_092 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4185 67 68, g32p_row03_traceSegment_092_4185_0067, g32p_row03_traceSegment_092_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_092_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_092 4050 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 4050 135 135, g32p_row03_traceSegment_092_4050_0135, g32p_row03_traceSegment_092_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_092 3780 540 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3780 270 270, g32p_row03_traceSegment_092_3780_0270, g32p_row03_traceSegment_092_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_092_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_092 3240 1080 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 3240 540 540, g32p_row03_traceSegment_092_3240_0540, g32p_row03_traceSegment_092_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_092_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_092 2160 2160 = [0, 0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 2160 1080 1080, g32p_row03_traceSegment_092_2160_1080, g32p_row03_traceSegment_092_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_092_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_092 0 4320 = [0, 0, 0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_092 0 2160 2160, g32p_row03_traceSegment_092_0000_2160, g32p_row03_traceSegment_092_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 92 = [0, 0, 0, 0, 40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_092_0000_4320

end HodgeLean.Foundations.Program

end
end
