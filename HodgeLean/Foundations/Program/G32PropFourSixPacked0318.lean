import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_018 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 18 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_018_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 16 8 9, g32p_row03_traceSegment_018_0016_0008, g32p_row03_traceSegment_018_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 0 16 17, g32p_row03_traceSegment_018_0000_0016, g32p_row03_traceSegment_018_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 33 8 9, g32p_row03_traceSegment_018_0033_0008, g32p_row03_traceSegment_018_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 50 8 9, g32p_row03_traceSegment_018_0050_0008, g32p_row03_traceSegment_018_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 33 17 17, g32p_row03_traceSegment_018_0033_0017, g32p_row03_traceSegment_018_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 0 33 34, g32p_row03_traceSegment_018_0000_0033, g32p_row03_traceSegment_018_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 67 8 9, g32p_row03_traceSegment_018_0067_0008, g32p_row03_traceSegment_018_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 84 8 9, g32p_row03_traceSegment_018_0084_0008, g32p_row03_traceSegment_018_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 67 17 17, g32p_row03_traceSegment_018_0067_0017, g32p_row03_traceSegment_018_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 101 8 9, g32p_row03_traceSegment_018_0101_0008, g32p_row03_traceSegment_018_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 118 8 9, g32p_row03_traceSegment_018_0118_0008, g32p_row03_traceSegment_018_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 101 17 17, g32p_row03_traceSegment_018_0101_0017, g32p_row03_traceSegment_018_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 67 34 34, g32p_row03_traceSegment_018_0067_0034, g32p_row03_traceSegment_018_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 0 67 68, g32p_row03_traceSegment_018_0000_0067, g32p_row03_traceSegment_018_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 151 8 9, g32p_row03_traceSegment_018_0151_0008, g32p_row03_traceSegment_018_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 135 16 17, g32p_row03_traceSegment_018_0135_0016, g32p_row03_traceSegment_018_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 168 8 9, g32p_row03_traceSegment_018_0168_0008, g32p_row03_traceSegment_018_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 185 8 9, g32p_row03_traceSegment_018_0185_0008, g32p_row03_traceSegment_018_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 168 17 17, g32p_row03_traceSegment_018_0168_0017, g32p_row03_traceSegment_018_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 135 33 34, g32p_row03_traceSegment_018_0135_0033, g32p_row03_traceSegment_018_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 202 8 9, g32p_row03_traceSegment_018_0202_0008, g32p_row03_traceSegment_018_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 219 8 9, g32p_row03_traceSegment_018_0219_0008, g32p_row03_traceSegment_018_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 202 17 17, g32p_row03_traceSegment_018_0202_0017, g32p_row03_traceSegment_018_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 236 8 9, g32p_row03_traceSegment_018_0236_0008, g32p_row03_traceSegment_018_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 253 8 9, g32p_row03_traceSegment_018_0253_0008, g32p_row03_traceSegment_018_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 236 17 17, g32p_row03_traceSegment_018_0236_0017, g32p_row03_traceSegment_018_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 202 34 34, g32p_row03_traceSegment_018_0202_0034, g32p_row03_traceSegment_018_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 135 67 68, g32p_row03_traceSegment_018_0135_0067, g32p_row03_traceSegment_018_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 0 135 135, g32p_row03_traceSegment_018_0000_0135, g32p_row03_traceSegment_018_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 286 8 9, g32p_row03_traceSegment_018_0286_0008, g32p_row03_traceSegment_018_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 270 16 17, g32p_row03_traceSegment_018_0270_0016, g32p_row03_traceSegment_018_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 303 8 9, g32p_row03_traceSegment_018_0303_0008, g32p_row03_traceSegment_018_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 320 8 9, g32p_row03_traceSegment_018_0320_0008, g32p_row03_traceSegment_018_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 303 17 17, g32p_row03_traceSegment_018_0303_0017, g32p_row03_traceSegment_018_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 270 33 34, g32p_row03_traceSegment_018_0270_0033, g32p_row03_traceSegment_018_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 337 8 9, g32p_row03_traceSegment_018_0337_0008, g32p_row03_traceSegment_018_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 354 8 9, g32p_row03_traceSegment_018_0354_0008, g32p_row03_traceSegment_018_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 337 17 17, g32p_row03_traceSegment_018_0337_0017, g32p_row03_traceSegment_018_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 371 8 9, g32p_row03_traceSegment_018_0371_0008, g32p_row03_traceSegment_018_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 388 8 9, g32p_row03_traceSegment_018_0388_0008, g32p_row03_traceSegment_018_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 371 17 17, g32p_row03_traceSegment_018_0371_0017, g32p_row03_traceSegment_018_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 337 34 34, g32p_row03_traceSegment_018_0337_0034, g32p_row03_traceSegment_018_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 270 67 68, g32p_row03_traceSegment_018_0270_0067, g32p_row03_traceSegment_018_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 421 8 9, g32p_row03_traceSegment_018_0421_0008, g32p_row03_traceSegment_018_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 405 16 17, g32p_row03_traceSegment_018_0405_0016, g32p_row03_traceSegment_018_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 438 8 9, g32p_row03_traceSegment_018_0438_0008, g32p_row03_traceSegment_018_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 455 8 9, g32p_row03_traceSegment_018_0455_0008, g32p_row03_traceSegment_018_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 438 17 17, g32p_row03_traceSegment_018_0438_0017, g32p_row03_traceSegment_018_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 405 33 34, g32p_row03_traceSegment_018_0405_0033, g32p_row03_traceSegment_018_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 472 8 9, g32p_row03_traceSegment_018_0472_0008, g32p_row03_traceSegment_018_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 489 8 9, g32p_row03_traceSegment_018_0489_0008, g32p_row03_traceSegment_018_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 472 17 17, g32p_row03_traceSegment_018_0472_0017, g32p_row03_traceSegment_018_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 506 8 9, g32p_row03_traceSegment_018_0506_0008, g32p_row03_traceSegment_018_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 523 8 9, g32p_row03_traceSegment_018_0523_0008, g32p_row03_traceSegment_018_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 506 17 17, g32p_row03_traceSegment_018_0506_0017, g32p_row03_traceSegment_018_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 472 34 34, g32p_row03_traceSegment_018_0472_0034, g32p_row03_traceSegment_018_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 405 67 68, g32p_row03_traceSegment_018_0405_0067, g32p_row03_traceSegment_018_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 270 135 135, g32p_row03_traceSegment_018_0270_0135, g32p_row03_traceSegment_018_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_018 0 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 0 270 270, g32p_row03_traceSegment_018_0000_0270, g32p_row03_traceSegment_018_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 556 8 9, g32p_row03_traceSegment_018_0556_0008, g32p_row03_traceSegment_018_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 540 16 17, g32p_row03_traceSegment_018_0540_0016, g32p_row03_traceSegment_018_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 573 8 9, g32p_row03_traceSegment_018_0573_0008, g32p_row03_traceSegment_018_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 590 8 9, g32p_row03_traceSegment_018_0590_0008, g32p_row03_traceSegment_018_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 573 17 17, g32p_row03_traceSegment_018_0573_0017, g32p_row03_traceSegment_018_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 540 33 34, g32p_row03_traceSegment_018_0540_0033, g32p_row03_traceSegment_018_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 607 8 9, g32p_row03_traceSegment_018_0607_0008, g32p_row03_traceSegment_018_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 624 8 9, g32p_row03_traceSegment_018_0624_0008, g32p_row03_traceSegment_018_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 607 17 17, g32p_row03_traceSegment_018_0607_0017, g32p_row03_traceSegment_018_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 641 8 9, g32p_row03_traceSegment_018_0641_0008, g32p_row03_traceSegment_018_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 658 8 9, g32p_row03_traceSegment_018_0658_0008, g32p_row03_traceSegment_018_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 641 17 17, g32p_row03_traceSegment_018_0641_0017, g32p_row03_traceSegment_018_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 607 34 34, g32p_row03_traceSegment_018_0607_0034, g32p_row03_traceSegment_018_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 540 67 68, g32p_row03_traceSegment_018_0540_0067, g32p_row03_traceSegment_018_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 691 8 9, g32p_row03_traceSegment_018_0691_0008, g32p_row03_traceSegment_018_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 675 16 17, g32p_row03_traceSegment_018_0675_0016, g32p_row03_traceSegment_018_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 708 8 9, g32p_row03_traceSegment_018_0708_0008, g32p_row03_traceSegment_018_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 725 8 9, g32p_row03_traceSegment_018_0725_0008, g32p_row03_traceSegment_018_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 708 17 17, g32p_row03_traceSegment_018_0708_0017, g32p_row03_traceSegment_018_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 675 33 34, g32p_row03_traceSegment_018_0675_0033, g32p_row03_traceSegment_018_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 742 8 9, g32p_row03_traceSegment_018_0742_0008, g32p_row03_traceSegment_018_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 767 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 759 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 759 8 9, g32p_row03_traceSegment_018_0759_0008, g32p_row03_traceSegment_018_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 742 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 742 17 17, g32p_row03_traceSegment_018_0742_0017, g32p_row03_traceSegment_018_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 776 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 776 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 776 8 9, g32p_row03_traceSegment_018_0776_0008, g32p_row03_traceSegment_018_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 801 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 793 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 793 8 9, g32p_row03_traceSegment_018_0793_0008, g32p_row03_traceSegment_018_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 776 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 776 17 17, g32p_row03_traceSegment_018_0776_0017, g32p_row03_traceSegment_018_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 742 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 742 34 34, g32p_row03_traceSegment_018_0742_0034, g32p_row03_traceSegment_018_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 675 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 675 67 68, g32p_row03_traceSegment_018_0675_0067, g32p_row03_traceSegment_018_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 540 270 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 540 135 135, g32p_row03_traceSegment_018_0540_0135, g32p_row03_traceSegment_018_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 810 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 826 8 9, g32p_row03_traceSegment_018_0826_0008, g32p_row03_traceSegment_018_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 810 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 810 16 17, g32p_row03_traceSegment_018_0810_0016, g32p_row03_traceSegment_018_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 843 8 9, g32p_row03_traceSegment_018_0843_0008, g32p_row03_traceSegment_018_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 860 8 9, g32p_row03_traceSegment_018_0860_0008, g32p_row03_traceSegment_018_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 843 17 17, g32p_row03_traceSegment_018_0843_0017, g32p_row03_traceSegment_018_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 810 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 810 33 34, g32p_row03_traceSegment_018_0810_0033, g32p_row03_traceSegment_018_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 877 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 885 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 877 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 877 8 9, g32p_row03_traceSegment_018_0877_0008, g32p_row03_traceSegment_018_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 894 8 9, g32p_row03_traceSegment_018_0894_0008, g32p_row03_traceSegment_018_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 877 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 877 17 17, g32p_row03_traceSegment_018_0877_0017, g32p_row03_traceSegment_018_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 911 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 911 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 911 8 9, g32p_row03_traceSegment_018_0911_0008, g32p_row03_traceSegment_018_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 928 8 9, g32p_row03_traceSegment_018_0928_0008, g32p_row03_traceSegment_018_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 911 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 911 17 17, g32p_row03_traceSegment_018_0911_0017, g32p_row03_traceSegment_018_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 877 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 877 34 34, g32p_row03_traceSegment_018_0877_0034, g32p_row03_traceSegment_018_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 810 135 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 810 67 68, g32p_row03_traceSegment_018_0810_0067, g32p_row03_traceSegment_018_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 961 8 9, g32p_row03_traceSegment_018_0961_0008, g32p_row03_traceSegment_018_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 945 16 17, g32p_row03_traceSegment_018_0945_0016, g32p_row03_traceSegment_018_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 978 8 9, g32p_row03_traceSegment_018_0978_0008, g32p_row03_traceSegment_018_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 995 8 9, g32p_row03_traceSegment_018_0995_0008, g32p_row03_traceSegment_018_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 978 17 17, g32p_row03_traceSegment_018_0978_0017, g32p_row03_traceSegment_018_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 945 33 34, g32p_row03_traceSegment_018_0945_0033, g32p_row03_traceSegment_018_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1012 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1020 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1012 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1012 8 9, g32p_row03_traceSegment_018_1012_0008, g32p_row03_traceSegment_018_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1029 8 9, g32p_row03_traceSegment_018_1029_0008, g32p_row03_traceSegment_018_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1012 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1012 17 17, g32p_row03_traceSegment_018_1012_0017, g32p_row03_traceSegment_018_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1046 8 9, g32p_row03_traceSegment_018_1046_0008, g32p_row03_traceSegment_018_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1071 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1063 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1063 8 9, g32p_row03_traceSegment_018_1063_0008, g32p_row03_traceSegment_018_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1046 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1046 17 17, g32p_row03_traceSegment_018_1046_0017, g32p_row03_traceSegment_018_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 1012 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1012 34 34, g32p_row03_traceSegment_018_1012_0034, g32p_row03_traceSegment_018_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 945 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 945 67 68, g32p_row03_traceSegment_018_0945_0067, g32p_row03_traceSegment_018_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 810 270 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 810 135 135, g32p_row03_traceSegment_018_0810_0135, g32p_row03_traceSegment_018_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_018 540 540 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 540 270 270, g32p_row03_traceSegment_018_0540_0270, g32p_row03_traceSegment_018_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_018 0 1080 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 0 540 540, g32p_row03_traceSegment_018_0000_0540, g32p_row03_traceSegment_018_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1096 8 9, g32p_row03_traceSegment_018_1096_0008, g32p_row03_traceSegment_018_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1080 16 17, g32p_row03_traceSegment_018_1080_0016, g32p_row03_traceSegment_018_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1113 8 9, g32p_row03_traceSegment_018_1113_0008, g32p_row03_traceSegment_018_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1130 8 9, g32p_row03_traceSegment_018_1130_0008, g32p_row03_traceSegment_018_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1113 17 17, g32p_row03_traceSegment_018_1113_0017, g32p_row03_traceSegment_018_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1080 33 34, g32p_row03_traceSegment_018_1080_0033, g32p_row03_traceSegment_018_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1147 8 9, g32p_row03_traceSegment_018_1147_0008, g32p_row03_traceSegment_018_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1164 8 9, g32p_row03_traceSegment_018_1164_0008, g32p_row03_traceSegment_018_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1147 17 17, g32p_row03_traceSegment_018_1147_0017, g32p_row03_traceSegment_018_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1181 8 9, g32p_row03_traceSegment_018_1181_0008, g32p_row03_traceSegment_018_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1198 8 9, g32p_row03_traceSegment_018_1198_0008, g32p_row03_traceSegment_018_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1181 17 17, g32p_row03_traceSegment_018_1181_0017, g32p_row03_traceSegment_018_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1147 34 34, g32p_row03_traceSegment_018_1147_0034, g32p_row03_traceSegment_018_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1080 67 68, g32p_row03_traceSegment_018_1080_0067, g32p_row03_traceSegment_018_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1231 8 9, g32p_row03_traceSegment_018_1231_0008, g32p_row03_traceSegment_018_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1215 16 17, g32p_row03_traceSegment_018_1215_0016, g32p_row03_traceSegment_018_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1248 8 9, g32p_row03_traceSegment_018_1248_0008, g32p_row03_traceSegment_018_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1265 8 9, g32p_row03_traceSegment_018_1265_0008, g32p_row03_traceSegment_018_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1248 17 17, g32p_row03_traceSegment_018_1248_0017, g32p_row03_traceSegment_018_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1215 33 34, g32p_row03_traceSegment_018_1215_0033, g32p_row03_traceSegment_018_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1282 8 9, g32p_row03_traceSegment_018_1282_0008, g32p_row03_traceSegment_018_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1299 8 9, g32p_row03_traceSegment_018_1299_0008, g32p_row03_traceSegment_018_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1282 17 17, g32p_row03_traceSegment_018_1282_0017, g32p_row03_traceSegment_018_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1316 8 9, g32p_row03_traceSegment_018_1316_0008, g32p_row03_traceSegment_018_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1333 8 9, g32p_row03_traceSegment_018_1333_0008, g32p_row03_traceSegment_018_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1316 17 17, g32p_row03_traceSegment_018_1316_0017, g32p_row03_traceSegment_018_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1282 34 34, g32p_row03_traceSegment_018_1282_0034, g32p_row03_traceSegment_018_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1215 67 68, g32p_row03_traceSegment_018_1215_0067, g32p_row03_traceSegment_018_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1080 135 135, g32p_row03_traceSegment_018_1080_0135, g32p_row03_traceSegment_018_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1366 8 9, g32p_row03_traceSegment_018_1366_0008, g32p_row03_traceSegment_018_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1350 16 17, g32p_row03_traceSegment_018_1350_0016, g32p_row03_traceSegment_018_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1383 8 9, g32p_row03_traceSegment_018_1383_0008, g32p_row03_traceSegment_018_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1400 8 9, g32p_row03_traceSegment_018_1400_0008, g32p_row03_traceSegment_018_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1383 17 17, g32p_row03_traceSegment_018_1383_0017, g32p_row03_traceSegment_018_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1350 33 34, g32p_row03_traceSegment_018_1350_0033, g32p_row03_traceSegment_018_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1425 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1417 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1417 8 9, g32p_row03_traceSegment_018_1417_0008, g32p_row03_traceSegment_018_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1434 8 9, g32p_row03_traceSegment_018_1434_0008, g32p_row03_traceSegment_018_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1417 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1417 17 17, g32p_row03_traceSegment_018_1417_0017, g32p_row03_traceSegment_018_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1451 8 9, g32p_row03_traceSegment_018_1451_0008, g32p_row03_traceSegment_018_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1468 8 9, g32p_row03_traceSegment_018_1468_0008, g32p_row03_traceSegment_018_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1451 17 17, g32p_row03_traceSegment_018_1451_0017, g32p_row03_traceSegment_018_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 1417 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1417 34 34, g32p_row03_traceSegment_018_1417_0034, g32p_row03_traceSegment_018_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 1350 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1350 67 68, g32p_row03_traceSegment_018_1350_0067, g32p_row03_traceSegment_018_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1501 8 9, g32p_row03_traceSegment_018_1501_0008, g32p_row03_traceSegment_018_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1485 16 17, g32p_row03_traceSegment_018_1485_0016, g32p_row03_traceSegment_018_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1518 8 9, g32p_row03_traceSegment_018_1518_0008, g32p_row03_traceSegment_018_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1535 8 9, g32p_row03_traceSegment_018_1535_0008, g32p_row03_traceSegment_018_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1518 17 17, g32p_row03_traceSegment_018_1518_0017, g32p_row03_traceSegment_018_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1485 33 34, g32p_row03_traceSegment_018_1485_0033, g32p_row03_traceSegment_018_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1552 8 9, g32p_row03_traceSegment_018_1552_0008, g32p_row03_traceSegment_018_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1577 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1569 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1569 8 9, g32p_row03_traceSegment_018_1569_0008, g32p_row03_traceSegment_018_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1552 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1552 17 17, g32p_row03_traceSegment_018_1552_0017, g32p_row03_traceSegment_018_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1586 8 9, g32p_row03_traceSegment_018_1586_0008, g32p_row03_traceSegment_018_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1603 8 9, g32p_row03_traceSegment_018_1603_0008, g32p_row03_traceSegment_018_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1586 17 17, g32p_row03_traceSegment_018_1586_0017, g32p_row03_traceSegment_018_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 1552 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1552 34 34, g32p_row03_traceSegment_018_1552_0034, g32p_row03_traceSegment_018_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 1485 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1485 67 68, g32p_row03_traceSegment_018_1485_0067, g32p_row03_traceSegment_018_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 1350 270 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1350 135 135, g32p_row03_traceSegment_018_1350_0135, g32p_row03_traceSegment_018_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_018 1080 540 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1080 270 270, g32p_row03_traceSegment_018_1080_0270, g32p_row03_traceSegment_018_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 1620 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1644 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1636 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1636 8 9, g32p_row03_traceSegment_018_1636_0008, g32p_row03_traceSegment_018_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 1620 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1620 16 17, g32p_row03_traceSegment_018_1620_0016, g32p_row03_traceSegment_018_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1653 8 9, g32p_row03_traceSegment_018_1653_0008, g32p_row03_traceSegment_018_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1670 8 9, g32p_row03_traceSegment_018_1670_0008, g32p_row03_traceSegment_018_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1653 17 17, g32p_row03_traceSegment_018_1653_0017, g32p_row03_traceSegment_018_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 1620 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1620 33 34, g32p_row03_traceSegment_018_1620_0033, g32p_row03_traceSegment_018_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1687 8 9, g32p_row03_traceSegment_018_1687_0008, g32p_row03_traceSegment_018_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1704 8 9, g32p_row03_traceSegment_018_1704_0008, g32p_row03_traceSegment_018_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1687 17 17, g32p_row03_traceSegment_018_1687_0017, g32p_row03_traceSegment_018_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1721 8 9, g32p_row03_traceSegment_018_1721_0008, g32p_row03_traceSegment_018_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1738 8 9, g32p_row03_traceSegment_018_1738_0008, g32p_row03_traceSegment_018_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1721 17 17, g32p_row03_traceSegment_018_1721_0017, g32p_row03_traceSegment_018_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1687 34 34, g32p_row03_traceSegment_018_1687_0034, g32p_row03_traceSegment_018_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 1620 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1620 67 68, g32p_row03_traceSegment_018_1620_0067, g32p_row03_traceSegment_018_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1771 8 9, g32p_row03_traceSegment_018_1771_0008, g32p_row03_traceSegment_018_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1755 16 17, g32p_row03_traceSegment_018_1755_0016, g32p_row03_traceSegment_018_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1788 8 9, g32p_row03_traceSegment_018_1788_0008, g32p_row03_traceSegment_018_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1805 8 9, g32p_row03_traceSegment_018_1805_0008, g32p_row03_traceSegment_018_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1788 17 17, g32p_row03_traceSegment_018_1788_0017, g32p_row03_traceSegment_018_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1755 33 34, g32p_row03_traceSegment_018_1755_0033, g32p_row03_traceSegment_018_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1830 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1822 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1822 8 9, g32p_row03_traceSegment_018_1822_0008, g32p_row03_traceSegment_018_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1839 8 9, g32p_row03_traceSegment_018_1839_0008, g32p_row03_traceSegment_018_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1822 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1822 17 17, g32p_row03_traceSegment_018_1822_0017, g32p_row03_traceSegment_018_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1856 8 9, g32p_row03_traceSegment_018_1856_0008, g32p_row03_traceSegment_018_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1873 8 9, g32p_row03_traceSegment_018_1873_0008, g32p_row03_traceSegment_018_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1856 17 17, g32p_row03_traceSegment_018_1856_0017, g32p_row03_traceSegment_018_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 1822 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1822 34 34, g32p_row03_traceSegment_018_1822_0034, g32p_row03_traceSegment_018_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 1755 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1755 67 68, g32p_row03_traceSegment_018_1755_0067, g32p_row03_traceSegment_018_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 1620 270 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1620 135 135, g32p_row03_traceSegment_018_1620_0135, g32p_row03_traceSegment_018_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1906 8 9, g32p_row03_traceSegment_018_1906_0008, g32p_row03_traceSegment_018_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1890 16 17, g32p_row03_traceSegment_018_1890_0016, g32p_row03_traceSegment_018_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1923 8 9, g32p_row03_traceSegment_018_1923_0008, g32p_row03_traceSegment_018_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1940 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1940 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1940 8 9, g32p_row03_traceSegment_018_1940_0008, g32p_row03_traceSegment_018_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1923 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1923 17 17, g32p_row03_traceSegment_018_1923_0017, g32p_row03_traceSegment_018_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 1890 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1890 33 34, g32p_row03_traceSegment_018_1890_0033, g32p_row03_traceSegment_018_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1957 8 9, g32p_row03_traceSegment_018_1957_0008, g32p_row03_traceSegment_018_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1974 8 9, g32p_row03_traceSegment_018_1974_0008, g32p_row03_traceSegment_018_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1957 17 17, g32p_row03_traceSegment_018_1957_0017, g32p_row03_traceSegment_018_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1991 8 9, g32p_row03_traceSegment_018_1991_0008, g32p_row03_traceSegment_018_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2008 8 9, g32p_row03_traceSegment_018_2008_0008, g32p_row03_traceSegment_018_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1991 17 17, g32p_row03_traceSegment_018_1991_0017, g32p_row03_traceSegment_018_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1957 34 34, g32p_row03_traceSegment_018_1957_0034, g32p_row03_traceSegment_018_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 1890 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1890 67 68, g32p_row03_traceSegment_018_1890_0067, g32p_row03_traceSegment_018_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2041 8 9, g32p_row03_traceSegment_018_2041_0008, g32p_row03_traceSegment_018_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2025 16 17, g32p_row03_traceSegment_018_2025_0016, g32p_row03_traceSegment_018_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2058 8 9, g32p_row03_traceSegment_018_2058_0008, g32p_row03_traceSegment_018_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2075 8 9, g32p_row03_traceSegment_018_2075_0008, g32p_row03_traceSegment_018_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2058 17 17, g32p_row03_traceSegment_018_2058_0017, g32p_row03_traceSegment_018_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2025 33 34, g32p_row03_traceSegment_018_2025_0033, g32p_row03_traceSegment_018_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2092 8 9, g32p_row03_traceSegment_018_2092_0008, g32p_row03_traceSegment_018_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2109 8 9, g32p_row03_traceSegment_018_2109_0008, g32p_row03_traceSegment_018_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2092 17 17, g32p_row03_traceSegment_018_2092_0017, g32p_row03_traceSegment_018_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2126 8 9, g32p_row03_traceSegment_018_2126_0008, g32p_row03_traceSegment_018_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2143 8 9, g32p_row03_traceSegment_018_2143_0008, g32p_row03_traceSegment_018_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2126 17 17, g32p_row03_traceSegment_018_2126_0017, g32p_row03_traceSegment_018_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2092 34 34, g32p_row03_traceSegment_018_2092_0034, g32p_row03_traceSegment_018_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2025 67 68, g32p_row03_traceSegment_018_2025_0067, g32p_row03_traceSegment_018_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 1890 270 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1890 135 135, g32p_row03_traceSegment_018_1890_0135, g32p_row03_traceSegment_018_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_018 1620 540 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1620 270 270, g32p_row03_traceSegment_018_1620_0270, g32p_row03_traceSegment_018_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_018_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_018 1080 1080 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 1080 540 540, g32p_row03_traceSegment_018_1080_0540, g32p_row03_traceSegment_018_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_018 0 2160 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 0 1080 1080, g32p_row03_traceSegment_018_0000_1080, g32p_row03_traceSegment_018_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2176 8 9, g32p_row03_traceSegment_018_2176_0008, g32p_row03_traceSegment_018_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2160 16 17, g32p_row03_traceSegment_018_2160_0016, g32p_row03_traceSegment_018_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2193 8 9, g32p_row03_traceSegment_018_2193_0008, g32p_row03_traceSegment_018_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2210 8 9, g32p_row03_traceSegment_018_2210_0008, g32p_row03_traceSegment_018_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2193 17 17, g32p_row03_traceSegment_018_2193_0017, g32p_row03_traceSegment_018_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2160 33 34, g32p_row03_traceSegment_018_2160_0033, g32p_row03_traceSegment_018_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2227 8 9, g32p_row03_traceSegment_018_2227_0008, g32p_row03_traceSegment_018_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2244 8 9, g32p_row03_traceSegment_018_2244_0008, g32p_row03_traceSegment_018_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2227 17 17, g32p_row03_traceSegment_018_2227_0017, g32p_row03_traceSegment_018_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2261 8 9, g32p_row03_traceSegment_018_2261_0008, g32p_row03_traceSegment_018_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2278 8 9, g32p_row03_traceSegment_018_2278_0008, g32p_row03_traceSegment_018_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2261 17 17, g32p_row03_traceSegment_018_2261_0017, g32p_row03_traceSegment_018_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2227 34 34, g32p_row03_traceSegment_018_2227_0034, g32p_row03_traceSegment_018_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2160 67 68, g32p_row03_traceSegment_018_2160_0067, g32p_row03_traceSegment_018_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2311 8 9, g32p_row03_traceSegment_018_2311_0008, g32p_row03_traceSegment_018_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2295 16 17, g32p_row03_traceSegment_018_2295_0016, g32p_row03_traceSegment_018_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2328 8 9, g32p_row03_traceSegment_018_2328_0008, g32p_row03_traceSegment_018_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2345 8 9, g32p_row03_traceSegment_018_2345_0008, g32p_row03_traceSegment_018_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2328 17 17, g32p_row03_traceSegment_018_2328_0017, g32p_row03_traceSegment_018_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2295 33 34, g32p_row03_traceSegment_018_2295_0033, g32p_row03_traceSegment_018_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2362 8 9, g32p_row03_traceSegment_018_2362_0008, g32p_row03_traceSegment_018_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2379 8 9, g32p_row03_traceSegment_018_2379_0008, g32p_row03_traceSegment_018_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2362 17 17, g32p_row03_traceSegment_018_2362_0017, g32p_row03_traceSegment_018_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2396 8 9, g32p_row03_traceSegment_018_2396_0008, g32p_row03_traceSegment_018_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2413 8 9, g32p_row03_traceSegment_018_2413_0008, g32p_row03_traceSegment_018_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2396 17 17, g32p_row03_traceSegment_018_2396_0017, g32p_row03_traceSegment_018_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2362 34 34, g32p_row03_traceSegment_018_2362_0034, g32p_row03_traceSegment_018_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2295 67 68, g32p_row03_traceSegment_018_2295_0067, g32p_row03_traceSegment_018_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 2160 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2160 135 135, g32p_row03_traceSegment_018_2160_0135, g32p_row03_traceSegment_018_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2446 8 9, g32p_row03_traceSegment_018_2446_0008, g32p_row03_traceSegment_018_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2430 16 17, g32p_row03_traceSegment_018_2430_0016, g32p_row03_traceSegment_018_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2463 8 9, g32p_row03_traceSegment_018_2463_0008, g32p_row03_traceSegment_018_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2480 8 9, g32p_row03_traceSegment_018_2480_0008, g32p_row03_traceSegment_018_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2463 17 17, g32p_row03_traceSegment_018_2463_0017, g32p_row03_traceSegment_018_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2430 33 34, g32p_row03_traceSegment_018_2430_0033, g32p_row03_traceSegment_018_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2497 8 9, g32p_row03_traceSegment_018_2497_0008, g32p_row03_traceSegment_018_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2514 8 9, g32p_row03_traceSegment_018_2514_0008, g32p_row03_traceSegment_018_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2497 17 17, g32p_row03_traceSegment_018_2497_0017, g32p_row03_traceSegment_018_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2531 8 9, g32p_row03_traceSegment_018_2531_0008, g32p_row03_traceSegment_018_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2548 8 9, g32p_row03_traceSegment_018_2548_0008, g32p_row03_traceSegment_018_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2531 17 17, g32p_row03_traceSegment_018_2531_0017, g32p_row03_traceSegment_018_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2497 34 34, g32p_row03_traceSegment_018_2497_0034, g32p_row03_traceSegment_018_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2430 67 68, g32p_row03_traceSegment_018_2430_0067, g32p_row03_traceSegment_018_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2581 8 9, g32p_row03_traceSegment_018_2581_0008, g32p_row03_traceSegment_018_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2565 16 17, g32p_row03_traceSegment_018_2565_0016, g32p_row03_traceSegment_018_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2598 8 9, g32p_row03_traceSegment_018_2598_0008, g32p_row03_traceSegment_018_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2615 8 9, g32p_row03_traceSegment_018_2615_0008, g32p_row03_traceSegment_018_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2598 17 17, g32p_row03_traceSegment_018_2598_0017, g32p_row03_traceSegment_018_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2565 33 34, g32p_row03_traceSegment_018_2565_0033, g32p_row03_traceSegment_018_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2632 8 9, g32p_row03_traceSegment_018_2632_0008, g32p_row03_traceSegment_018_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2649 8 9, g32p_row03_traceSegment_018_2649_0008, g32p_row03_traceSegment_018_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2632 17 17, g32p_row03_traceSegment_018_2632_0017, g32p_row03_traceSegment_018_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2666 8 9, g32p_row03_traceSegment_018_2666_0008, g32p_row03_traceSegment_018_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2683 8 9, g32p_row03_traceSegment_018_2683_0008, g32p_row03_traceSegment_018_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2666 17 17, g32p_row03_traceSegment_018_2666_0017, g32p_row03_traceSegment_018_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2632 34 34, g32p_row03_traceSegment_018_2632_0034, g32p_row03_traceSegment_018_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2565 67 68, g32p_row03_traceSegment_018_2565_0067, g32p_row03_traceSegment_018_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2430 135 135, g32p_row03_traceSegment_018_2430_0135, g32p_row03_traceSegment_018_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_018 2160 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2160 270 270, g32p_row03_traceSegment_018_2160_0270, g32p_row03_traceSegment_018_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2716 8 9, g32p_row03_traceSegment_018_2716_0008, g32p_row03_traceSegment_018_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2700 16 17, g32p_row03_traceSegment_018_2700_0016, g32p_row03_traceSegment_018_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2733 8 9, g32p_row03_traceSegment_018_2733_0008, g32p_row03_traceSegment_018_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2750 8 9, g32p_row03_traceSegment_018_2750_0008, g32p_row03_traceSegment_018_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2733 17 17, g32p_row03_traceSegment_018_2733_0017, g32p_row03_traceSegment_018_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2700 33 34, g32p_row03_traceSegment_018_2700_0033, g32p_row03_traceSegment_018_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2767 8 9, g32p_row03_traceSegment_018_2767_0008, g32p_row03_traceSegment_018_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2784 8 9, g32p_row03_traceSegment_018_2784_0008, g32p_row03_traceSegment_018_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2767 17 17, g32p_row03_traceSegment_018_2767_0017, g32p_row03_traceSegment_018_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2801 8 9, g32p_row03_traceSegment_018_2801_0008, g32p_row03_traceSegment_018_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2818 8 9, g32p_row03_traceSegment_018_2818_0008, g32p_row03_traceSegment_018_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2801 17 17, g32p_row03_traceSegment_018_2801_0017, g32p_row03_traceSegment_018_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2767 34 34, g32p_row03_traceSegment_018_2767_0034, g32p_row03_traceSegment_018_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2700 67 68, g32p_row03_traceSegment_018_2700_0067, g32p_row03_traceSegment_018_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2851 8 9, g32p_row03_traceSegment_018_2851_0008, g32p_row03_traceSegment_018_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2835 16 17, g32p_row03_traceSegment_018_2835_0016, g32p_row03_traceSegment_018_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2868 8 9, g32p_row03_traceSegment_018_2868_0008, g32p_row03_traceSegment_018_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2885 8 9, g32p_row03_traceSegment_018_2885_0008, g32p_row03_traceSegment_018_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2868 17 17, g32p_row03_traceSegment_018_2868_0017, g32p_row03_traceSegment_018_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2835 33 34, g32p_row03_traceSegment_018_2835_0033, g32p_row03_traceSegment_018_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2902 8 9, g32p_row03_traceSegment_018_2902_0008, g32p_row03_traceSegment_018_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2919 8 9, g32p_row03_traceSegment_018_2919_0008, g32p_row03_traceSegment_018_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2902 17 17, g32p_row03_traceSegment_018_2902_0017, g32p_row03_traceSegment_018_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2936 8 9, g32p_row03_traceSegment_018_2936_0008, g32p_row03_traceSegment_018_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2953 8 9, g32p_row03_traceSegment_018_2953_0008, g32p_row03_traceSegment_018_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2936 17 17, g32p_row03_traceSegment_018_2936_0017, g32p_row03_traceSegment_018_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2902 34 34, g32p_row03_traceSegment_018_2902_0034, g32p_row03_traceSegment_018_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2835 67 68, g32p_row03_traceSegment_018_2835_0067, g32p_row03_traceSegment_018_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2700 135 135, g32p_row03_traceSegment_018_2700_0135, g32p_row03_traceSegment_018_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2986 8 9, g32p_row03_traceSegment_018_2986_0008, g32p_row03_traceSegment_018_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2970 16 17, g32p_row03_traceSegment_018_2970_0016, g32p_row03_traceSegment_018_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3003 8 9, g32p_row03_traceSegment_018_3003_0008, g32p_row03_traceSegment_018_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3020 8 9, g32p_row03_traceSegment_018_3020_0008, g32p_row03_traceSegment_018_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3003 17 17, g32p_row03_traceSegment_018_3003_0017, g32p_row03_traceSegment_018_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2970 33 34, g32p_row03_traceSegment_018_2970_0033, g32p_row03_traceSegment_018_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3037 8 9, g32p_row03_traceSegment_018_3037_0008, g32p_row03_traceSegment_018_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3054 8 9, g32p_row03_traceSegment_018_3054_0008, g32p_row03_traceSegment_018_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3037 17 17, g32p_row03_traceSegment_018_3037_0017, g32p_row03_traceSegment_018_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3071 8 9, g32p_row03_traceSegment_018_3071_0008, g32p_row03_traceSegment_018_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3088 8 9, g32p_row03_traceSegment_018_3088_0008, g32p_row03_traceSegment_018_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3071 17 17, g32p_row03_traceSegment_018_3071_0017, g32p_row03_traceSegment_018_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3037 34 34, g32p_row03_traceSegment_018_3037_0034, g32p_row03_traceSegment_018_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2970 67 68, g32p_row03_traceSegment_018_2970_0067, g32p_row03_traceSegment_018_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3121 8 9, g32p_row03_traceSegment_018_3121_0008, g32p_row03_traceSegment_018_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3105 16 17, g32p_row03_traceSegment_018_3105_0016, g32p_row03_traceSegment_018_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3138 8 9, g32p_row03_traceSegment_018_3138_0008, g32p_row03_traceSegment_018_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3155 8 9, g32p_row03_traceSegment_018_3155_0008, g32p_row03_traceSegment_018_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3138 17 17, g32p_row03_traceSegment_018_3138_0017, g32p_row03_traceSegment_018_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3105 33 34, g32p_row03_traceSegment_018_3105_0033, g32p_row03_traceSegment_018_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3172 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3172 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3172 8 9, g32p_row03_traceSegment_018_3172_0008, g32p_row03_traceSegment_018_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3189 8 9, g32p_row03_traceSegment_018_3189_0008, g32p_row03_traceSegment_018_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3172 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3172 17 17, g32p_row03_traceSegment_018_3172_0017, g32p_row03_traceSegment_018_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3206 8 9, g32p_row03_traceSegment_018_3206_0008, g32p_row03_traceSegment_018_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3223 8 9, g32p_row03_traceSegment_018_3223_0008, g32p_row03_traceSegment_018_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3206 17 17, g32p_row03_traceSegment_018_3206_0017, g32p_row03_traceSegment_018_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 3172 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3172 34 34, g32p_row03_traceSegment_018_3172_0034, g32p_row03_traceSegment_018_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 3105 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3105 67 68, g32p_row03_traceSegment_018_3105_0067, g32p_row03_traceSegment_018_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 2970 270 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2970 135 135, g32p_row03_traceSegment_018_2970_0135, g32p_row03_traceSegment_018_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_018 2700 540 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2700 270 270, g32p_row03_traceSegment_018_2700_0270, g32p_row03_traceSegment_018_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_018 2160 1080 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2160 540 540, g32p_row03_traceSegment_018_2160_0540, g32p_row03_traceSegment_018_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3256 8 9, g32p_row03_traceSegment_018_3256_0008, g32p_row03_traceSegment_018_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3240 16 17, g32p_row03_traceSegment_018_3240_0016, g32p_row03_traceSegment_018_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3273 8 9, g32p_row03_traceSegment_018_3273_0008, g32p_row03_traceSegment_018_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3290 8 9, g32p_row03_traceSegment_018_3290_0008, g32p_row03_traceSegment_018_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3273 17 17, g32p_row03_traceSegment_018_3273_0017, g32p_row03_traceSegment_018_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3240 33 34, g32p_row03_traceSegment_018_3240_0033, g32p_row03_traceSegment_018_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3307 8 9, g32p_row03_traceSegment_018_3307_0008, g32p_row03_traceSegment_018_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3324 8 9, g32p_row03_traceSegment_018_3324_0008, g32p_row03_traceSegment_018_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3307 17 17, g32p_row03_traceSegment_018_3307_0017, g32p_row03_traceSegment_018_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3341 8 9, g32p_row03_traceSegment_018_3341_0008, g32p_row03_traceSegment_018_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3358 8 9, g32p_row03_traceSegment_018_3358_0008, g32p_row03_traceSegment_018_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3341 17 17, g32p_row03_traceSegment_018_3341_0017, g32p_row03_traceSegment_018_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3307 34 34, g32p_row03_traceSegment_018_3307_0034, g32p_row03_traceSegment_018_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3240 67 68, g32p_row03_traceSegment_018_3240_0067, g32p_row03_traceSegment_018_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 3375 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3391 8 9, g32p_row03_traceSegment_018_3391_0008, g32p_row03_traceSegment_018_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 3375 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3375 16 17, g32p_row03_traceSegment_018_3375_0016, g32p_row03_traceSegment_018_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3408 8 9, g32p_row03_traceSegment_018_3408_0008, g32p_row03_traceSegment_018_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3425 8 9, g32p_row03_traceSegment_018_3425_0008, g32p_row03_traceSegment_018_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3408 17 17, g32p_row03_traceSegment_018_3408_0017, g32p_row03_traceSegment_018_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 3375 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3375 33 34, g32p_row03_traceSegment_018_3375_0033, g32p_row03_traceSegment_018_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3442 8 9, g32p_row03_traceSegment_018_3442_0008, g32p_row03_traceSegment_018_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3459 8 9, g32p_row03_traceSegment_018_3459_0008, g32p_row03_traceSegment_018_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3442 17 17, g32p_row03_traceSegment_018_3442_0017, g32p_row03_traceSegment_018_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3476 8 9, g32p_row03_traceSegment_018_3476_0008, g32p_row03_traceSegment_018_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3493 8 9, g32p_row03_traceSegment_018_3493_0008, g32p_row03_traceSegment_018_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3476 17 17, g32p_row03_traceSegment_018_3476_0017, g32p_row03_traceSegment_018_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3442 34 34, g32p_row03_traceSegment_018_3442_0034, g32p_row03_traceSegment_018_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 3375 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3375 67 68, g32p_row03_traceSegment_018_3375_0067, g32p_row03_traceSegment_018_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 3240 270 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3240 135 135, g32p_row03_traceSegment_018_3240_0135, g32p_row03_traceSegment_018_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 3510 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3526 8 9, g32p_row03_traceSegment_018_3526_0008, g32p_row03_traceSegment_018_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 3510 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3510 16 17, g32p_row03_traceSegment_018_3510_0016, g32p_row03_traceSegment_018_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3543 8 9, g32p_row03_traceSegment_018_3543_0008, g32p_row03_traceSegment_018_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3568 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3560 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3560 8 9, g32p_row03_traceSegment_018_3560_0008, g32p_row03_traceSegment_018_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3543 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3543 17 17, g32p_row03_traceSegment_018_3543_0017, g32p_row03_traceSegment_018_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 3510 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3510 33 34, g32p_row03_traceSegment_018_3510_0033, g32p_row03_traceSegment_018_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3577 8 9, g32p_row03_traceSegment_018_3577_0008, g32p_row03_traceSegment_018_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3594 8 9, g32p_row03_traceSegment_018_3594_0008, g32p_row03_traceSegment_018_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3577 17 17, g32p_row03_traceSegment_018_3577_0017, g32p_row03_traceSegment_018_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3611 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3611 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3611 8 9, g32p_row03_traceSegment_018_3611_0008, g32p_row03_traceSegment_018_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3628 8 9, g32p_row03_traceSegment_018_3628_0008, g32p_row03_traceSegment_018_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3611 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3611 17 17, g32p_row03_traceSegment_018_3611_0017, g32p_row03_traceSegment_018_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 3577 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3577 34 34, g32p_row03_traceSegment_018_3577_0034, g32p_row03_traceSegment_018_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 3510 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3510 67 68, g32p_row03_traceSegment_018_3510_0067, g32p_row03_traceSegment_018_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3661 8 9, g32p_row03_traceSegment_018_3661_0008, g32p_row03_traceSegment_018_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3645 16 17, g32p_row03_traceSegment_018_3645_0016, g32p_row03_traceSegment_018_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3678 8 9, g32p_row03_traceSegment_018_3678_0008, g32p_row03_traceSegment_018_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3695 8 9, g32p_row03_traceSegment_018_3695_0008, g32p_row03_traceSegment_018_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3678 17 17, g32p_row03_traceSegment_018_3678_0017, g32p_row03_traceSegment_018_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3645 33 34, g32p_row03_traceSegment_018_3645_0033, g32p_row03_traceSegment_018_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3712 8 9, g32p_row03_traceSegment_018_3712_0008, g32p_row03_traceSegment_018_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3729 8 9, g32p_row03_traceSegment_018_3729_0008, g32p_row03_traceSegment_018_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3712 17 17, g32p_row03_traceSegment_018_3712_0017, g32p_row03_traceSegment_018_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3754 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3746 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3746 8 9, g32p_row03_traceSegment_018_3746_0008, g32p_row03_traceSegment_018_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3763 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3763 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3763 8 9, g32p_row03_traceSegment_018_3763_0008, g32p_row03_traceSegment_018_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3746 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3746 17 17, g32p_row03_traceSegment_018_3746_0017, g32p_row03_traceSegment_018_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 3712 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3712 34 34, g32p_row03_traceSegment_018_3712_0034, g32p_row03_traceSegment_018_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 3645 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3645 67 68, g32p_row03_traceSegment_018_3645_0067, g32p_row03_traceSegment_018_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 3510 270 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3510 135 135, g32p_row03_traceSegment_018_3510_0135, g32p_row03_traceSegment_018_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_018 3240 540 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3240 270 270, g32p_row03_traceSegment_018_3240_0270, g32p_row03_traceSegment_018_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 3780 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3796 8 9, g32p_row03_traceSegment_018_3796_0008, g32p_row03_traceSegment_018_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 3780 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3780 16 17, g32p_row03_traceSegment_018_3780_0016, g32p_row03_traceSegment_018_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3813 8 9, g32p_row03_traceSegment_018_3813_0008, g32p_row03_traceSegment_018_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3830 8 9, g32p_row03_traceSegment_018_3830_0008, g32p_row03_traceSegment_018_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3813 17 17, g32p_row03_traceSegment_018_3813_0017, g32p_row03_traceSegment_018_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 3780 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3780 33 34, g32p_row03_traceSegment_018_3780_0033, g32p_row03_traceSegment_018_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3847 8 9, g32p_row03_traceSegment_018_3847_0008, g32p_row03_traceSegment_018_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3864 8 9, g32p_row03_traceSegment_018_3864_0008, g32p_row03_traceSegment_018_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3847 17 17, g32p_row03_traceSegment_018_3847_0017, g32p_row03_traceSegment_018_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3889 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3881 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3881 8 9, g32p_row03_traceSegment_018_3881_0008, g32p_row03_traceSegment_018_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3898 8 9, g32p_row03_traceSegment_018_3898_0008, g32p_row03_traceSegment_018_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3881 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3881 17 17, g32p_row03_traceSegment_018_3881_0017, g32p_row03_traceSegment_018_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 3847 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3847 34 34, g32p_row03_traceSegment_018_3847_0034, g32p_row03_traceSegment_018_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 3780 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3780 67 68, g32p_row03_traceSegment_018_3780_0067, g32p_row03_traceSegment_018_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3939 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3931 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3931 8 9, g32p_row03_traceSegment_018_3931_0008, g32p_row03_traceSegment_018_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 3915 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3915 16 17, g32p_row03_traceSegment_018_3915_0016, g32p_row03_traceSegment_018_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3948 8 9, g32p_row03_traceSegment_018_3948_0008, g32p_row03_traceSegment_018_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3965 8 9, g32p_row03_traceSegment_018_3965_0008, g32p_row03_traceSegment_018_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3948 17 17, g32p_row03_traceSegment_018_3948_0017, g32p_row03_traceSegment_018_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 3915 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3915 33 34, g32p_row03_traceSegment_018_3915_0033, g32p_row03_traceSegment_018_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3982 8 9, g32p_row03_traceSegment_018_3982_0008, g32p_row03_traceSegment_018_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3999 8 9, g32p_row03_traceSegment_018_3999_0008, g32p_row03_traceSegment_018_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3982 17 17, g32p_row03_traceSegment_018_3982_0017, g32p_row03_traceSegment_018_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4016 8 9, g32p_row03_traceSegment_018_4016_0008, g32p_row03_traceSegment_018_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4033 8 9, g32p_row03_traceSegment_018_4033_0008, g32p_row03_traceSegment_018_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4016 17 17, g32p_row03_traceSegment_018_4016_0017, g32p_row03_traceSegment_018_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3982 34 34, g32p_row03_traceSegment_018_3982_0034, g32p_row03_traceSegment_018_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 3915 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3915 67 68, g32p_row03_traceSegment_018_3915_0067, g32p_row03_traceSegment_018_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 3780 270 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3780 135 135, g32p_row03_traceSegment_018_3780_0135, g32p_row03_traceSegment_018_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 4050 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4066 8 9, g32p_row03_traceSegment_018_4066_0008, g32p_row03_traceSegment_018_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 4050 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4050 16 17, g32p_row03_traceSegment_018_4050_0016, g32p_row03_traceSegment_018_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4083 8 9, g32p_row03_traceSegment_018_4083_0008, g32p_row03_traceSegment_018_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4100 8 9, g32p_row03_traceSegment_018_4100_0008, g32p_row03_traceSegment_018_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4083 17 17, g32p_row03_traceSegment_018_4083_0017, g32p_row03_traceSegment_018_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 4050 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4050 33 34, g32p_row03_traceSegment_018_4050_0033, g32p_row03_traceSegment_018_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4117 8 9, g32p_row03_traceSegment_018_4117_0008, g32p_row03_traceSegment_018_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4134 8 9, g32p_row03_traceSegment_018_4134_0008, g32p_row03_traceSegment_018_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4117 17 17, g32p_row03_traceSegment_018_4117_0017, g32p_row03_traceSegment_018_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4151 8 9, g32p_row03_traceSegment_018_4151_0008, g32p_row03_traceSegment_018_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4168 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4168 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4168 8 9, g32p_row03_traceSegment_018_4168_0008, g32p_row03_traceSegment_018_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 4151 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4151 17 17, g32p_row03_traceSegment_018_4151_0017, g32p_row03_traceSegment_018_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 4117 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4117 34 34, g32p_row03_traceSegment_018_4117_0034, g32p_row03_traceSegment_018_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 4050 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4050 67 68, g32p_row03_traceSegment_018_4050_0067, g32p_row03_traceSegment_018_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_018 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4201 8 9, g32p_row03_traceSegment_018_4201_0008, g32p_row03_traceSegment_018_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_018 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4185 16 17, g32p_row03_traceSegment_018_4185_0016, g32p_row03_traceSegment_018_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4218 8 9, g32p_row03_traceSegment_018_4218_0008, g32p_row03_traceSegment_018_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4235 8 9, g32p_row03_traceSegment_018_4235_0008, g32p_row03_traceSegment_018_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4218 17 17, g32p_row03_traceSegment_018_4218_0017, g32p_row03_traceSegment_018_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_018 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4185 33 34, g32p_row03_traceSegment_018_4185_0033, g32p_row03_traceSegment_018_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4252 8 9, g32p_row03_traceSegment_018_4252_0008, g32p_row03_traceSegment_018_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4269 8 9, g32p_row03_traceSegment_018_4269_0008, g32p_row03_traceSegment_018_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4252 17 17, g32p_row03_traceSegment_018_4252_0017, g32p_row03_traceSegment_018_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4286 8 9, g32p_row03_traceSegment_018_4286_0008, g32p_row03_traceSegment_018_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_018 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_018 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_018_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_018 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4303 8 9, g32p_row03_traceSegment_018_4303_0008, g32p_row03_traceSegment_018_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_018 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4286 17 17, g32p_row03_traceSegment_018_4286_0017, g32p_row03_traceSegment_018_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_018 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4252 34 34, g32p_row03_traceSegment_018_4252_0034, g32p_row03_traceSegment_018_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_018 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4185 67 68, g32p_row03_traceSegment_018_4185_0067, g32p_row03_traceSegment_018_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_018_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_018 4050 270 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 4050 135 135, g32p_row03_traceSegment_018_4050_0135, g32p_row03_traceSegment_018_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_018 3780 540 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3780 270 270, g32p_row03_traceSegment_018_3780_0270, g32p_row03_traceSegment_018_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_018_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_018 3240 1080 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 3240 540 540, g32p_row03_traceSegment_018_3240_0540, g32p_row03_traceSegment_018_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_018_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_018 2160 2160 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 2160 1080 1080, g32p_row03_traceSegment_018_2160_1080, g32p_row03_traceSegment_018_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_018_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_018 0 4320 = [0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_018 0 2160 2160, g32p_row03_traceSegment_018_0000_2160, g32p_row03_traceSegment_018_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 18 = [0, 0, 0, 30] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_018_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_021 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 21 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_021_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 16 8 9, g32p_row03_traceSegment_021_0016_0008, g32p_row03_traceSegment_021_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 0 16 17, g32p_row03_traceSegment_021_0000_0016, g32p_row03_traceSegment_021_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 33 8 9, g32p_row03_traceSegment_021_0033_0008, g32p_row03_traceSegment_021_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 50 8 9, g32p_row03_traceSegment_021_0050_0008, g32p_row03_traceSegment_021_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 33 17 17, g32p_row03_traceSegment_021_0033_0017, g32p_row03_traceSegment_021_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 0 33 34, g32p_row03_traceSegment_021_0000_0033, g32p_row03_traceSegment_021_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 67 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 75 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 67 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 67 8 9, g32p_row03_traceSegment_021_0067_0008, g32p_row03_traceSegment_021_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 84 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 92 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 84 17 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 84 8 9, g32p_row03_traceSegment_021_0084_0008, g32p_row03_traceSegment_021_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 67 34 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 67 17 17, g32p_row03_traceSegment_021_0067_0017, g32p_row03_traceSegment_021_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 101 8 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 101 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 101 8 9, g32p_row03_traceSegment_021_0101_0008, g32p_row03_traceSegment_021_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 118 8 9, g32p_row03_traceSegment_021_0118_0008, g32p_row03_traceSegment_021_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 101 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 101 17 17, g32p_row03_traceSegment_021_0101_0017, g32p_row03_traceSegment_021_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 67 68 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 67 34 34, g32p_row03_traceSegment_021_0067_0034, g32p_row03_traceSegment_021_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 0 135 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 0 67 68, g32p_row03_traceSegment_021_0000_0067, g32p_row03_traceSegment_021_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 151 8 9, g32p_row03_traceSegment_021_0151_0008, g32p_row03_traceSegment_021_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 135 16 17, g32p_row03_traceSegment_021_0135_0016, g32p_row03_traceSegment_021_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 168 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 168 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 168 8 9, g32p_row03_traceSegment_021_0168_0008, g32p_row03_traceSegment_021_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 193 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 185 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 185 8 9, g32p_row03_traceSegment_021_0185_0008, g32p_row03_traceSegment_021_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 168 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 168 17 17, g32p_row03_traceSegment_021_0168_0017, g32p_row03_traceSegment_021_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 135 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 135 33 34, g32p_row03_traceSegment_021_0135_0033, g32p_row03_traceSegment_021_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 210 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 202 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 202 8 9, g32p_row03_traceSegment_021_0202_0008, g32p_row03_traceSegment_021_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 219 8 9, g32p_row03_traceSegment_021_0219_0008, g32p_row03_traceSegment_021_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 202 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 202 17 17, g32p_row03_traceSegment_021_0202_0017, g32p_row03_traceSegment_021_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 236 8 9, g32p_row03_traceSegment_021_0236_0008, g32p_row03_traceSegment_021_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 253 8 9, g32p_row03_traceSegment_021_0253_0008, g32p_row03_traceSegment_021_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 236 17 17, g32p_row03_traceSegment_021_0236_0017, g32p_row03_traceSegment_021_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 202 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 202 34 34, g32p_row03_traceSegment_021_0202_0034, g32p_row03_traceSegment_021_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 135 135 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 135 67 68, g32p_row03_traceSegment_021_0135_0067, g32p_row03_traceSegment_021_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 0 270 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 0 135 135, g32p_row03_traceSegment_021_0000_0135, g32p_row03_traceSegment_021_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 286 8 9, g32p_row03_traceSegment_021_0286_0008, g32p_row03_traceSegment_021_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 270 16 17, g32p_row03_traceSegment_021_0270_0016, g32p_row03_traceSegment_021_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 303 8 9, g32p_row03_traceSegment_021_0303_0008, g32p_row03_traceSegment_021_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 320 8 9, g32p_row03_traceSegment_021_0320_0008, g32p_row03_traceSegment_021_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 303 17 17, g32p_row03_traceSegment_021_0303_0017, g32p_row03_traceSegment_021_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 270 33 34, g32p_row03_traceSegment_021_0270_0033, g32p_row03_traceSegment_021_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 337 8 9, g32p_row03_traceSegment_021_0337_0008, g32p_row03_traceSegment_021_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 354 8 9, g32p_row03_traceSegment_021_0354_0008, g32p_row03_traceSegment_021_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 337 17 17, g32p_row03_traceSegment_021_0337_0017, g32p_row03_traceSegment_021_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 371 8 9, g32p_row03_traceSegment_021_0371_0008, g32p_row03_traceSegment_021_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 388 8 9, g32p_row03_traceSegment_021_0388_0008, g32p_row03_traceSegment_021_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 371 17 17, g32p_row03_traceSegment_021_0371_0017, g32p_row03_traceSegment_021_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 337 34 34, g32p_row03_traceSegment_021_0337_0034, g32p_row03_traceSegment_021_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 270 67 68, g32p_row03_traceSegment_021_0270_0067, g32p_row03_traceSegment_021_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 421 8 9, g32p_row03_traceSegment_021_0421_0008, g32p_row03_traceSegment_021_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 405 16 17, g32p_row03_traceSegment_021_0405_0016, g32p_row03_traceSegment_021_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 446 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 438 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 438 8 9, g32p_row03_traceSegment_021_0438_0008, g32p_row03_traceSegment_021_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 455 8 9, g32p_row03_traceSegment_021_0455_0008, g32p_row03_traceSegment_021_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 438 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 438 17 17, g32p_row03_traceSegment_021_0438_0017, g32p_row03_traceSegment_021_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 405 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 405 33 34, g32p_row03_traceSegment_021_0405_0033, g32p_row03_traceSegment_021_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 472 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 472 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 472 8 9, g32p_row03_traceSegment_021_0472_0008, g32p_row03_traceSegment_021_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 489 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 497 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 489 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 489 8 9, g32p_row03_traceSegment_021_0489_0008, g32p_row03_traceSegment_021_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 472 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 472 17 17, g32p_row03_traceSegment_021_0472_0017, g32p_row03_traceSegment_021_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 514 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 506 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 506 8 9, g32p_row03_traceSegment_021_0506_0008, g32p_row03_traceSegment_021_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 523 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 523 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 523 8 9, g32p_row03_traceSegment_021_0523_0008, g32p_row03_traceSegment_021_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 506 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 506 17 17, g32p_row03_traceSegment_021_0506_0017, g32p_row03_traceSegment_021_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 472 68 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 472 34 34, g32p_row03_traceSegment_021_0472_0034, g32p_row03_traceSegment_021_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 405 135 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 405 67 68, g32p_row03_traceSegment_021_0405_0067, g32p_row03_traceSegment_021_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 270 270 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 270 135 135, g32p_row03_traceSegment_021_0270_0135, g32p_row03_traceSegment_021_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_021 0 540 = [0, 0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 0 270 270, g32p_row03_traceSegment_021_0000_0270, g32p_row03_traceSegment_021_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 540 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 564 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 556 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 556 8 9, g32p_row03_traceSegment_021_0556_0008, g32p_row03_traceSegment_021_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 540 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 540 16 17, g32p_row03_traceSegment_021_0540_0016, g32p_row03_traceSegment_021_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 573 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 573 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 573 8 9, g32p_row03_traceSegment_021_0573_0008, g32p_row03_traceSegment_021_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 590 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 598 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 590 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 590 8 9, g32p_row03_traceSegment_021_0590_0008, g32p_row03_traceSegment_021_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 573 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 573 17 17, g32p_row03_traceSegment_021_0573_0017, g32p_row03_traceSegment_021_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 540 67 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 540 33 34, g32p_row03_traceSegment_021_0540_0033, g32p_row03_traceSegment_021_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 607 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 615 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 607 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 607 8 9, g32p_row03_traceSegment_021_0607_0008, g32p_row03_traceSegment_021_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 624 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 632 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 624 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 624 8 9, g32p_row03_traceSegment_021_0624_0008, g32p_row03_traceSegment_021_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 607 34 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 607 17 17, g32p_row03_traceSegment_021_0607_0017, g32p_row03_traceSegment_021_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 649 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 641 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 641 8 9, g32p_row03_traceSegment_021_0641_0008, g32p_row03_traceSegment_021_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 658 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 666 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 658 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 658 8 9, g32p_row03_traceSegment_021_0658_0008, g32p_row03_traceSegment_021_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 641 34 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 641 17 17, g32p_row03_traceSegment_021_0641_0017, g32p_row03_traceSegment_021_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 607 68 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 607 34 34, g32p_row03_traceSegment_021_0607_0034, g32p_row03_traceSegment_021_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 540 135 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 540 67 68, g32p_row03_traceSegment_021_0540_0067, g32p_row03_traceSegment_021_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 675 16 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 699 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 691 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 691 8 9, g32p_row03_traceSegment_021_0691_0008, g32p_row03_traceSegment_021_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 675 33 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 675 16 17, g32p_row03_traceSegment_021_0675_0016, g32p_row03_traceSegment_021_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 708 8 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 716 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 708 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 708 8 9, g32p_row03_traceSegment_021_0708_0008, g32p_row03_traceSegment_021_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 725 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 733 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 725 17 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 725 8 9, g32p_row03_traceSegment_021_0725_0008, g32p_row03_traceSegment_021_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 708 34 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 708 17 17, g32p_row03_traceSegment_021_0708_0017, g32p_row03_traceSegment_021_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 675 67 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 675 33 34, g32p_row03_traceSegment_021_0675_0033, g32p_row03_traceSegment_021_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 742 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 750 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 742 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 742 8 9, g32p_row03_traceSegment_021_0742_0008, g32p_row03_traceSegment_021_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 759 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 767 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 759 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 759 8 9, g32p_row03_traceSegment_021_0759_0008, g32p_row03_traceSegment_021_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 742 34 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 742 17 17, g32p_row03_traceSegment_021_0742_0017, g32p_row03_traceSegment_021_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 776 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 784 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 776 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 776 8 9, g32p_row03_traceSegment_021_0776_0008, g32p_row03_traceSegment_021_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 793 8 9, g32p_row03_traceSegment_021_0793_0008, g32p_row03_traceSegment_021_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 776 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 776 17 17, g32p_row03_traceSegment_021_0776_0017, g32p_row03_traceSegment_021_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 742 68 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 742 34 34, g32p_row03_traceSegment_021_0742_0034, g32p_row03_traceSegment_021_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 675 135 = [0, 0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 675 67 68, g32p_row03_traceSegment_021_0675_0067, g32p_row03_traceSegment_021_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 540 270 = [0, 0, 0, 42] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 540 135 135, g32p_row03_traceSegment_021_0540_0135, g32p_row03_traceSegment_021_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 810 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 826 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 826 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 826 8 9, g32p_row03_traceSegment_021_0826_0008, g32p_row03_traceSegment_021_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 810 33 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 810 16 17, g32p_row03_traceSegment_021_0810_0016, g32p_row03_traceSegment_021_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 843 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 843 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 843 8 9, g32p_row03_traceSegment_021_0843_0008, g32p_row03_traceSegment_021_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 860 8 9, g32p_row03_traceSegment_021_0860_0008, g32p_row03_traceSegment_021_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 843 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 843 17 17, g32p_row03_traceSegment_021_0843_0017, g32p_row03_traceSegment_021_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 810 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 810 33 34, g32p_row03_traceSegment_021_0810_0033, g32p_row03_traceSegment_021_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 877 8 9, g32p_row03_traceSegment_021_0877_0008, g32p_row03_traceSegment_021_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 894 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 894 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 894 8 9, g32p_row03_traceSegment_021_0894_0008, g32p_row03_traceSegment_021_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 877 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 877 17 17, g32p_row03_traceSegment_021_0877_0017, g32p_row03_traceSegment_021_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 919 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 911 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 911 8 9, g32p_row03_traceSegment_021_0911_0008, g32p_row03_traceSegment_021_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 928 8 9, g32p_row03_traceSegment_021_0928_0008, g32p_row03_traceSegment_021_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 911 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 911 17 17, g32p_row03_traceSegment_021_0911_0017, g32p_row03_traceSegment_021_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 877 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 877 34 34, g32p_row03_traceSegment_021_0877_0034, g32p_row03_traceSegment_021_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 810 135 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 810 67 68, g32p_row03_traceSegment_021_0810_0067, g32p_row03_traceSegment_021_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 961 8 9, g32p_row03_traceSegment_021_0961_0008, g32p_row03_traceSegment_021_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 945 16 17, g32p_row03_traceSegment_021_0945_0016, g32p_row03_traceSegment_021_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 978 8 9, g32p_row03_traceSegment_021_0978_0008, g32p_row03_traceSegment_021_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 995 8 9, g32p_row03_traceSegment_021_0995_0008, g32p_row03_traceSegment_021_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 978 17 17, g32p_row03_traceSegment_021_0978_0017, g32p_row03_traceSegment_021_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 945 33 34, g32p_row03_traceSegment_021_0945_0033, g32p_row03_traceSegment_021_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1012 8 9, g32p_row03_traceSegment_021_1012_0008, g32p_row03_traceSegment_021_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1029 8 9, g32p_row03_traceSegment_021_1029_0008, g32p_row03_traceSegment_021_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1012 17 17, g32p_row03_traceSegment_021_1012_0017, g32p_row03_traceSegment_021_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1046 8 9, g32p_row03_traceSegment_021_1046_0008, g32p_row03_traceSegment_021_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1063 8 9, g32p_row03_traceSegment_021_1063_0008, g32p_row03_traceSegment_021_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1046 17 17, g32p_row03_traceSegment_021_1046_0017, g32p_row03_traceSegment_021_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1012 34 34, g32p_row03_traceSegment_021_1012_0034, g32p_row03_traceSegment_021_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 945 67 68, g32p_row03_traceSegment_021_0945_0067, g32p_row03_traceSegment_021_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 810 270 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 810 135 135, g32p_row03_traceSegment_021_0810_0135, g32p_row03_traceSegment_021_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_021 540 540 = [0, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 540 270 270, g32p_row03_traceSegment_021_0540_0270, g32p_row03_traceSegment_021_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_021 0 1080 = [0, 0, 0, 70] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 0 540 540, g32p_row03_traceSegment_021_0000_0540, g32p_row03_traceSegment_021_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1096 8 9, g32p_row03_traceSegment_021_1096_0008, g32p_row03_traceSegment_021_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1080 16 17, g32p_row03_traceSegment_021_1080_0016, g32p_row03_traceSegment_021_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1113 8 9, g32p_row03_traceSegment_021_1113_0008, g32p_row03_traceSegment_021_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1130 8 9, g32p_row03_traceSegment_021_1130_0008, g32p_row03_traceSegment_021_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1113 17 17, g32p_row03_traceSegment_021_1113_0017, g32p_row03_traceSegment_021_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1080 33 34, g32p_row03_traceSegment_021_1080_0033, g32p_row03_traceSegment_021_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1147 8 9, g32p_row03_traceSegment_021_1147_0008, g32p_row03_traceSegment_021_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1164 8 9, g32p_row03_traceSegment_021_1164_0008, g32p_row03_traceSegment_021_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1147 17 17, g32p_row03_traceSegment_021_1147_0017, g32p_row03_traceSegment_021_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1181 8 9, g32p_row03_traceSegment_021_1181_0008, g32p_row03_traceSegment_021_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1198 8 9, g32p_row03_traceSegment_021_1198_0008, g32p_row03_traceSegment_021_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1181 17 17, g32p_row03_traceSegment_021_1181_0017, g32p_row03_traceSegment_021_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1147 34 34, g32p_row03_traceSegment_021_1147_0034, g32p_row03_traceSegment_021_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1080 67 68, g32p_row03_traceSegment_021_1080_0067, g32p_row03_traceSegment_021_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1231 8 9, g32p_row03_traceSegment_021_1231_0008, g32p_row03_traceSegment_021_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1215 16 17, g32p_row03_traceSegment_021_1215_0016, g32p_row03_traceSegment_021_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1248 8 9, g32p_row03_traceSegment_021_1248_0008, g32p_row03_traceSegment_021_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1273 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1265 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1265 8 9, g32p_row03_traceSegment_021_1265_0008, g32p_row03_traceSegment_021_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1248 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1248 17 17, g32p_row03_traceSegment_021_1248_0017, g32p_row03_traceSegment_021_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 1215 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1215 33 34, g32p_row03_traceSegment_021_1215_0033, g32p_row03_traceSegment_021_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1290 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1282 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1282 8 9, g32p_row03_traceSegment_021_1282_0008, g32p_row03_traceSegment_021_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1307 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1299 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1299 8 9, g32p_row03_traceSegment_021_1299_0008, g32p_row03_traceSegment_021_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1282 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1282 17 17, g32p_row03_traceSegment_021_1282_0017, g32p_row03_traceSegment_021_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1324 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1316 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1316 8 9, g32p_row03_traceSegment_021_1316_0008, g32p_row03_traceSegment_021_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1333 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1333 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1333 8 9, g32p_row03_traceSegment_021_1333_0008, g32p_row03_traceSegment_021_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1316 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1316 17 17, g32p_row03_traceSegment_021_1316_0017, g32p_row03_traceSegment_021_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 1282 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1282 34 34, g32p_row03_traceSegment_021_1282_0034, g32p_row03_traceSegment_021_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 1215 135 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1215 67 68, g32p_row03_traceSegment_021_1215_0067, g32p_row03_traceSegment_021_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 1080 270 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1080 135 135, g32p_row03_traceSegment_021_1080_0135, g32p_row03_traceSegment_021_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 1350 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1366 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1366 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1366 8 9, g32p_row03_traceSegment_021_1366_0008, g32p_row03_traceSegment_021_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 1350 33 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1350 16 17, g32p_row03_traceSegment_021_1350_0016, g32p_row03_traceSegment_021_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1383 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1391 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1383 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1383 8 9, g32p_row03_traceSegment_021_1383_0008, g32p_row03_traceSegment_021_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1408 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1400 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1400 8 9, g32p_row03_traceSegment_021_1400_0008, g32p_row03_traceSegment_021_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1383 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1383 17 17, g32p_row03_traceSegment_021_1383_0017, g32p_row03_traceSegment_021_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 1350 67 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1350 33 34, g32p_row03_traceSegment_021_1350_0033, g32p_row03_traceSegment_021_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1417 8 9, g32p_row03_traceSegment_021_1417_0008, g32p_row03_traceSegment_021_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1434 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1434 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1434 8 9, g32p_row03_traceSegment_021_1434_0008, g32p_row03_traceSegment_021_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1417 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1417 17 17, g32p_row03_traceSegment_021_1417_0017, g32p_row03_traceSegment_021_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1451 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1459 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1451 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1451 8 9, g32p_row03_traceSegment_021_1451_0008, g32p_row03_traceSegment_021_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1468 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1476 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1468 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1468 8 9, g32p_row03_traceSegment_021_1468_0008, g32p_row03_traceSegment_021_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1451 34 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1451 17 17, g32p_row03_traceSegment_021_1451_0017, g32p_row03_traceSegment_021_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 1417 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1417 34 34, g32p_row03_traceSegment_021_1417_0034, g32p_row03_traceSegment_021_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 1350 135 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1350 67 68, g32p_row03_traceSegment_021_1350_0067, g32p_row03_traceSegment_021_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 1485 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1501 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1501 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1501 8 9, g32p_row03_traceSegment_021_1501_0008, g32p_row03_traceSegment_021_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 1485 33 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1485 16 17, g32p_row03_traceSegment_021_1485_0016, g32p_row03_traceSegment_021_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1526 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1518 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1518 8 9, g32p_row03_traceSegment_021_1518_0008, g32p_row03_traceSegment_021_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1535 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1543 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1535 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1535 8 9, g32p_row03_traceSegment_021_1535_0008, g32p_row03_traceSegment_021_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1518 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1518 17 17, g32p_row03_traceSegment_021_1518_0017, g32p_row03_traceSegment_021_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 1485 67 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1485 33 34, g32p_row03_traceSegment_021_1485_0033, g32p_row03_traceSegment_021_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1552 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1560 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1552 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1552 8 9, g32p_row03_traceSegment_021_1552_0008, g32p_row03_traceSegment_021_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1577 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1569 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1569 8 9, g32p_row03_traceSegment_021_1569_0008, g32p_row03_traceSegment_021_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1552 34 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1552 17 17, g32p_row03_traceSegment_021_1552_0017, g32p_row03_traceSegment_021_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1586 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1586 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1586 8 9, g32p_row03_traceSegment_021_1586_0008, g32p_row03_traceSegment_021_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1611 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1603 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1603 8 9, g32p_row03_traceSegment_021_1603_0008, g32p_row03_traceSegment_021_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1586 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1586 17 17, g32p_row03_traceSegment_021_1586_0017, g32p_row03_traceSegment_021_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 1552 68 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1552 34 34, g32p_row03_traceSegment_021_1552_0034, g32p_row03_traceSegment_021_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 1485 135 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1485 67 68, g32p_row03_traceSegment_021_1485_0067, g32p_row03_traceSegment_021_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 1350 270 = [0, 0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1350 135 135, g32p_row03_traceSegment_021_1350_0135, g32p_row03_traceSegment_021_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_021 1080 540 = [0, 0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1080 270 270, g32p_row03_traceSegment_021_1080_0270, g32p_row03_traceSegment_021_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 1620 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1636 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1644 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1636 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1636 8 9, g32p_row03_traceSegment_021_1636_0008, g32p_row03_traceSegment_021_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 1620 33 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1620 16 17, g32p_row03_traceSegment_021_1620_0016, g32p_row03_traceSegment_021_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1653 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1661 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1653 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1653 8 9, g32p_row03_traceSegment_021_1653_0008, g32p_row03_traceSegment_021_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1678 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1670 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1670 8 9, g32p_row03_traceSegment_021_1670_0008, g32p_row03_traceSegment_021_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1653 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1653 17 17, g32p_row03_traceSegment_021_1653_0017, g32p_row03_traceSegment_021_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 1620 67 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1620 33 34, g32p_row03_traceSegment_021_1620_0033, g32p_row03_traceSegment_021_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1687 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1695 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1687 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1687 8 9, g32p_row03_traceSegment_021_1687_0008, g32p_row03_traceSegment_021_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1704 8 9, g32p_row03_traceSegment_021_1704_0008, g32p_row03_traceSegment_021_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1687 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1687 17 17, g32p_row03_traceSegment_021_1687_0017, g32p_row03_traceSegment_021_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1721 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1729 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1721 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1721 8 9, g32p_row03_traceSegment_021_1721_0008, g32p_row03_traceSegment_021_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1738 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1746 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1738 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1738 8 9, g32p_row03_traceSegment_021_1738_0008, g32p_row03_traceSegment_021_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1721 34 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1721 17 17, g32p_row03_traceSegment_021_1721_0017, g32p_row03_traceSegment_021_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 1687 68 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1687 34 34, g32p_row03_traceSegment_021_1687_0034, g32p_row03_traceSegment_021_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 1620 135 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1620 67 68, g32p_row03_traceSegment_021_1620_0067, g32p_row03_traceSegment_021_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 1755 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1771 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1779 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1771 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1771 8 9, g32p_row03_traceSegment_021_1771_0008, g32p_row03_traceSegment_021_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 1755 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1755 16 17, g32p_row03_traceSegment_021_1755_0016, g32p_row03_traceSegment_021_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1788 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1796 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1788 17 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1788 8 9, g32p_row03_traceSegment_021_1788_0008, g32p_row03_traceSegment_021_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1805 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1813 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1805 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1805 8 9, g32p_row03_traceSegment_021_1805_0008, g32p_row03_traceSegment_021_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1788 34 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1788 17 17, g32p_row03_traceSegment_021_1788_0017, g32p_row03_traceSegment_021_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 1755 67 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1755 33 34, g32p_row03_traceSegment_021_1755_0033, g32p_row03_traceSegment_021_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1822 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1830 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1822 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1822 8 9, g32p_row03_traceSegment_021_1822_0008, g32p_row03_traceSegment_021_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1847 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1839 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1839 8 9, g32p_row03_traceSegment_021_1839_0008, g32p_row03_traceSegment_021_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1822 34 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1822 17 17, g32p_row03_traceSegment_021_1822_0017, g32p_row03_traceSegment_021_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1864 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1856 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1856 8 9, g32p_row03_traceSegment_021_1856_0008, g32p_row03_traceSegment_021_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1873 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1881 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1873 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1873 8 9, g32p_row03_traceSegment_021_1873_0008, g32p_row03_traceSegment_021_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1856 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1856 17 17, g32p_row03_traceSegment_021_1856_0017, g32p_row03_traceSegment_021_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 1822 68 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1822 34 34, g32p_row03_traceSegment_021_1822_0034, g32p_row03_traceSegment_021_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 1755 135 = [0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1755 67 68, g32p_row03_traceSegment_021_1755_0067, g32p_row03_traceSegment_021_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 1620 270 = [0, 0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1620 135 135, g32p_row03_traceSegment_021_1620_0135, g32p_row03_traceSegment_021_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 1890 16 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1906 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1914 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1906 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1906 8 9, g32p_row03_traceSegment_021_1906_0008, g32p_row03_traceSegment_021_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 1890 33 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1890 16 17, g32p_row03_traceSegment_021_1890_0016, g32p_row03_traceSegment_021_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1923 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1923 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1923 8 9, g32p_row03_traceSegment_021_1923_0008, g32p_row03_traceSegment_021_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1940 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1948 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1940 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1940 8 9, g32p_row03_traceSegment_021_1940_0008, g32p_row03_traceSegment_021_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1923 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1923 17 17, g32p_row03_traceSegment_021_1923_0017, g32p_row03_traceSegment_021_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 1890 67 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1890 33 34, g32p_row03_traceSegment_021_1890_0033, g32p_row03_traceSegment_021_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1957 8 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1965 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1957 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1957 8 9, g32p_row03_traceSegment_021_1957_0008, g32p_row03_traceSegment_021_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1974 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1982 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1974 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1974 8 9, g32p_row03_traceSegment_021_1974_0008, g32p_row03_traceSegment_021_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1957 34 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1957 17 17, g32p_row03_traceSegment_021_1957_0017, g32p_row03_traceSegment_021_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1991 8 9, g32p_row03_traceSegment_021_1991_0008, g32p_row03_traceSegment_021_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2008 8 9, g32p_row03_traceSegment_021_2008_0008, g32p_row03_traceSegment_021_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1991 17 17, g32p_row03_traceSegment_021_1991_0017, g32p_row03_traceSegment_021_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 1957 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1957 34 34, g32p_row03_traceSegment_021_1957_0034, g32p_row03_traceSegment_021_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 1890 135 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1890 67 68, g32p_row03_traceSegment_021_1890_0067, g32p_row03_traceSegment_021_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2041 8 9, g32p_row03_traceSegment_021_2041_0008, g32p_row03_traceSegment_021_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2025 16 17, g32p_row03_traceSegment_021_2025_0016, g32p_row03_traceSegment_021_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2058 8 9, g32p_row03_traceSegment_021_2058_0008, g32p_row03_traceSegment_021_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2075 8 9, g32p_row03_traceSegment_021_2075_0008, g32p_row03_traceSegment_021_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2058 17 17, g32p_row03_traceSegment_021_2058_0017, g32p_row03_traceSegment_021_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2025 33 34, g32p_row03_traceSegment_021_2025_0033, g32p_row03_traceSegment_021_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2092 8 9, g32p_row03_traceSegment_021_2092_0008, g32p_row03_traceSegment_021_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2109 8 9, g32p_row03_traceSegment_021_2109_0008, g32p_row03_traceSegment_021_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2092 17 17, g32p_row03_traceSegment_021_2092_0017, g32p_row03_traceSegment_021_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2126 8 9, g32p_row03_traceSegment_021_2126_0008, g32p_row03_traceSegment_021_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2143 8 9, g32p_row03_traceSegment_021_2143_0008, g32p_row03_traceSegment_021_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2126 17 17, g32p_row03_traceSegment_021_2126_0017, g32p_row03_traceSegment_021_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2092 34 34, g32p_row03_traceSegment_021_2092_0034, g32p_row03_traceSegment_021_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2025 67 68, g32p_row03_traceSegment_021_2025_0067, g32p_row03_traceSegment_021_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 1890 270 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1890 135 135, g32p_row03_traceSegment_021_1890_0135, g32p_row03_traceSegment_021_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_021 1620 540 = [0, 0, 0, 49] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1620 270 270, g32p_row03_traceSegment_021_1620_0270, g32p_row03_traceSegment_021_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_021_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_021 1080 1080 = [0, 0, 0, 83] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 1080 540 540, g32p_row03_traceSegment_021_1080_0540, g32p_row03_traceSegment_021_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_021 0 2160 = [0, 0, 0, 153] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 0 1080 1080, g32p_row03_traceSegment_021_0000_1080, g32p_row03_traceSegment_021_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2176 8 9, g32p_row03_traceSegment_021_2176_0008, g32p_row03_traceSegment_021_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2160 16 17, g32p_row03_traceSegment_021_2160_0016, g32p_row03_traceSegment_021_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2193 8 9, g32p_row03_traceSegment_021_2193_0008, g32p_row03_traceSegment_021_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2210 8 9, g32p_row03_traceSegment_021_2210_0008, g32p_row03_traceSegment_021_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2193 17 17, g32p_row03_traceSegment_021_2193_0017, g32p_row03_traceSegment_021_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2160 33 34, g32p_row03_traceSegment_021_2160_0033, g32p_row03_traceSegment_021_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2227 8 9, g32p_row03_traceSegment_021_2227_0008, g32p_row03_traceSegment_021_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2244 8 9, g32p_row03_traceSegment_021_2244_0008, g32p_row03_traceSegment_021_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2227 17 17, g32p_row03_traceSegment_021_2227_0017, g32p_row03_traceSegment_021_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2261 8 9, g32p_row03_traceSegment_021_2261_0008, g32p_row03_traceSegment_021_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2278 8 9, g32p_row03_traceSegment_021_2278_0008, g32p_row03_traceSegment_021_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2261 17 17, g32p_row03_traceSegment_021_2261_0017, g32p_row03_traceSegment_021_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2227 34 34, g32p_row03_traceSegment_021_2227_0034, g32p_row03_traceSegment_021_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2160 67 68, g32p_row03_traceSegment_021_2160_0067, g32p_row03_traceSegment_021_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2311 8 9, g32p_row03_traceSegment_021_2311_0008, g32p_row03_traceSegment_021_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2295 16 17, g32p_row03_traceSegment_021_2295_0016, g32p_row03_traceSegment_021_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2328 8 9, g32p_row03_traceSegment_021_2328_0008, g32p_row03_traceSegment_021_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2345 8 9, g32p_row03_traceSegment_021_2345_0008, g32p_row03_traceSegment_021_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2328 17 17, g32p_row03_traceSegment_021_2328_0017, g32p_row03_traceSegment_021_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2295 33 34, g32p_row03_traceSegment_021_2295_0033, g32p_row03_traceSegment_021_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2362 8 9, g32p_row03_traceSegment_021_2362_0008, g32p_row03_traceSegment_021_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2379 8 9, g32p_row03_traceSegment_021_2379_0008, g32p_row03_traceSegment_021_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2362 17 17, g32p_row03_traceSegment_021_2362_0017, g32p_row03_traceSegment_021_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2396 8 9, g32p_row03_traceSegment_021_2396_0008, g32p_row03_traceSegment_021_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2413 8 9, g32p_row03_traceSegment_021_2413_0008, g32p_row03_traceSegment_021_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2396 17 17, g32p_row03_traceSegment_021_2396_0017, g32p_row03_traceSegment_021_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2362 34 34, g32p_row03_traceSegment_021_2362_0034, g32p_row03_traceSegment_021_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2295 67 68, g32p_row03_traceSegment_021_2295_0067, g32p_row03_traceSegment_021_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 2160 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2160 135 135, g32p_row03_traceSegment_021_2160_0135, g32p_row03_traceSegment_021_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2446 8 9, g32p_row03_traceSegment_021_2446_0008, g32p_row03_traceSegment_021_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2430 16 17, g32p_row03_traceSegment_021_2430_0016, g32p_row03_traceSegment_021_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2463 8 9, g32p_row03_traceSegment_021_2463_0008, g32p_row03_traceSegment_021_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2480 8 9, g32p_row03_traceSegment_021_2480_0008, g32p_row03_traceSegment_021_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2463 17 17, g32p_row03_traceSegment_021_2463_0017, g32p_row03_traceSegment_021_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2430 33 34, g32p_row03_traceSegment_021_2430_0033, g32p_row03_traceSegment_021_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2497 8 9, g32p_row03_traceSegment_021_2497_0008, g32p_row03_traceSegment_021_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2514 8 9, g32p_row03_traceSegment_021_2514_0008, g32p_row03_traceSegment_021_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2497 17 17, g32p_row03_traceSegment_021_2497_0017, g32p_row03_traceSegment_021_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2531 8 9, g32p_row03_traceSegment_021_2531_0008, g32p_row03_traceSegment_021_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2548 8 9, g32p_row03_traceSegment_021_2548_0008, g32p_row03_traceSegment_021_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2531 17 17, g32p_row03_traceSegment_021_2531_0017, g32p_row03_traceSegment_021_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2497 34 34, g32p_row03_traceSegment_021_2497_0034, g32p_row03_traceSegment_021_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2430 67 68, g32p_row03_traceSegment_021_2430_0067, g32p_row03_traceSegment_021_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2581 8 9, g32p_row03_traceSegment_021_2581_0008, g32p_row03_traceSegment_021_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2565 16 17, g32p_row03_traceSegment_021_2565_0016, g32p_row03_traceSegment_021_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2598 8 9, g32p_row03_traceSegment_021_2598_0008, g32p_row03_traceSegment_021_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2615 8 9, g32p_row03_traceSegment_021_2615_0008, g32p_row03_traceSegment_021_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2598 17 17, g32p_row03_traceSegment_021_2598_0017, g32p_row03_traceSegment_021_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2565 33 34, g32p_row03_traceSegment_021_2565_0033, g32p_row03_traceSegment_021_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2632 8 9, g32p_row03_traceSegment_021_2632_0008, g32p_row03_traceSegment_021_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2649 8 9, g32p_row03_traceSegment_021_2649_0008, g32p_row03_traceSegment_021_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2632 17 17, g32p_row03_traceSegment_021_2632_0017, g32p_row03_traceSegment_021_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2666 8 9, g32p_row03_traceSegment_021_2666_0008, g32p_row03_traceSegment_021_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2683 8 9, g32p_row03_traceSegment_021_2683_0008, g32p_row03_traceSegment_021_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2666 17 17, g32p_row03_traceSegment_021_2666_0017, g32p_row03_traceSegment_021_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2632 34 34, g32p_row03_traceSegment_021_2632_0034, g32p_row03_traceSegment_021_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2565 67 68, g32p_row03_traceSegment_021_2565_0067, g32p_row03_traceSegment_021_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2430 135 135, g32p_row03_traceSegment_021_2430_0135, g32p_row03_traceSegment_021_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_021 2160 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2160 270 270, g32p_row03_traceSegment_021_2160_0270, g32p_row03_traceSegment_021_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2716 8 9, g32p_row03_traceSegment_021_2716_0008, g32p_row03_traceSegment_021_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2700 16 17, g32p_row03_traceSegment_021_2700_0016, g32p_row03_traceSegment_021_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2733 8 9, g32p_row03_traceSegment_021_2733_0008, g32p_row03_traceSegment_021_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2750 8 9, g32p_row03_traceSegment_021_2750_0008, g32p_row03_traceSegment_021_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2733 17 17, g32p_row03_traceSegment_021_2733_0017, g32p_row03_traceSegment_021_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2700 33 34, g32p_row03_traceSegment_021_2700_0033, g32p_row03_traceSegment_021_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2767 8 9, g32p_row03_traceSegment_021_2767_0008, g32p_row03_traceSegment_021_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2784 8 9, g32p_row03_traceSegment_021_2784_0008, g32p_row03_traceSegment_021_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2767 17 17, g32p_row03_traceSegment_021_2767_0017, g32p_row03_traceSegment_021_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2801 8 9, g32p_row03_traceSegment_021_2801_0008, g32p_row03_traceSegment_021_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2818 8 9, g32p_row03_traceSegment_021_2818_0008, g32p_row03_traceSegment_021_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2801 17 17, g32p_row03_traceSegment_021_2801_0017, g32p_row03_traceSegment_021_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2767 34 34, g32p_row03_traceSegment_021_2767_0034, g32p_row03_traceSegment_021_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2700 67 68, g32p_row03_traceSegment_021_2700_0067, g32p_row03_traceSegment_021_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2851 8 9, g32p_row03_traceSegment_021_2851_0008, g32p_row03_traceSegment_021_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2835 16 17, g32p_row03_traceSegment_021_2835_0016, g32p_row03_traceSegment_021_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2868 8 9, g32p_row03_traceSegment_021_2868_0008, g32p_row03_traceSegment_021_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2885 8 9, g32p_row03_traceSegment_021_2885_0008, g32p_row03_traceSegment_021_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2868 17 17, g32p_row03_traceSegment_021_2868_0017, g32p_row03_traceSegment_021_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2835 33 34, g32p_row03_traceSegment_021_2835_0033, g32p_row03_traceSegment_021_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2902 8 9, g32p_row03_traceSegment_021_2902_0008, g32p_row03_traceSegment_021_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2919 8 9, g32p_row03_traceSegment_021_2919_0008, g32p_row03_traceSegment_021_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2902 17 17, g32p_row03_traceSegment_021_2902_0017, g32p_row03_traceSegment_021_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2944 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2936 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2936 8 9, g32p_row03_traceSegment_021_2936_0008, g32p_row03_traceSegment_021_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2953 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2961 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2953 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2953 8 9, g32p_row03_traceSegment_021_2953_0008, g32p_row03_traceSegment_021_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 2936 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2936 17 17, g32p_row03_traceSegment_021_2936_0017, g32p_row03_traceSegment_021_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 2902 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2902 34 34, g32p_row03_traceSegment_021_2902_0034, g32p_row03_traceSegment_021_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 2835 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2835 67 68, g32p_row03_traceSegment_021_2835_0067, g32p_row03_traceSegment_021_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 2700 270 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2700 135 135, g32p_row03_traceSegment_021_2700_0135, g32p_row03_traceSegment_021_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 2970 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 2986 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 2994 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 2986 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2986 8 9, g32p_row03_traceSegment_021_2986_0008, g32p_row03_traceSegment_021_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 2970 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2970 16 17, g32p_row03_traceSegment_021_2970_0016, g32p_row03_traceSegment_021_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3003 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3011 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3003 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3003 8 9, g32p_row03_traceSegment_021_3003_0008, g32p_row03_traceSegment_021_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3020 8 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3028 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3020 17 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3020 8 9, g32p_row03_traceSegment_021_3020_0008, g32p_row03_traceSegment_021_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3003 34 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3003 17 17, g32p_row03_traceSegment_021_3003_0017, g32p_row03_traceSegment_021_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 2970 67 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2970 33 34, g32p_row03_traceSegment_021_2970_0033, g32p_row03_traceSegment_021_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3045 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3037 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3037 8 9, g32p_row03_traceSegment_021_3037_0008, g32p_row03_traceSegment_021_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3054 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3062 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3054 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3054 8 9, g32p_row03_traceSegment_021_3054_0008, g32p_row03_traceSegment_021_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3037 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3037 17 17, g32p_row03_traceSegment_021_3037_0017, g32p_row03_traceSegment_021_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3071 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3079 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3071 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3071 8 9, g32p_row03_traceSegment_021_3071_0008, g32p_row03_traceSegment_021_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3088 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3096 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3088 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3088 8 9, g32p_row03_traceSegment_021_3088_0008, g32p_row03_traceSegment_021_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3071 34 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3071 17 17, g32p_row03_traceSegment_021_3071_0017, g32p_row03_traceSegment_021_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 3037 68 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3037 34 34, g32p_row03_traceSegment_021_3037_0034, g32p_row03_traceSegment_021_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 2970 135 = [0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2970 67 68, g32p_row03_traceSegment_021_2970_0067, g32p_row03_traceSegment_021_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 3105 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3121 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3129 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3121 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3121 8 9, g32p_row03_traceSegment_021_3121_0008, g32p_row03_traceSegment_021_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 3105 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3105 16 17, g32p_row03_traceSegment_021_3105_0016, g32p_row03_traceSegment_021_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3138 8 9, g32p_row03_traceSegment_021_3138_0008, g32p_row03_traceSegment_021_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3163 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3155 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3155 8 9, g32p_row03_traceSegment_021_3155_0008, g32p_row03_traceSegment_021_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3138 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3138 17 17, g32p_row03_traceSegment_021_3138_0017, g32p_row03_traceSegment_021_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 3105 67 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3105 33 34, g32p_row03_traceSegment_021_3105_0033, g32p_row03_traceSegment_021_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3172 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3172 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3172 8 9, g32p_row03_traceSegment_021_3172_0008, g32p_row03_traceSegment_021_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3189 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3189 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3189 8 9, g32p_row03_traceSegment_021_3189_0008, g32p_row03_traceSegment_021_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3172 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3172 17 17, g32p_row03_traceSegment_021_3172_0017, g32p_row03_traceSegment_021_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3206 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3214 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3206 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3206 8 9, g32p_row03_traceSegment_021_3206_0008, g32p_row03_traceSegment_021_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3223 8 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3223 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3223 8 9, g32p_row03_traceSegment_021_3223_0008, g32p_row03_traceSegment_021_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3206 34 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3206 17 17, g32p_row03_traceSegment_021_3206_0017, g32p_row03_traceSegment_021_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 3172 68 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3172 34 34, g32p_row03_traceSegment_021_3172_0034, g32p_row03_traceSegment_021_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 3105 135 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3105 67 68, g32p_row03_traceSegment_021_3105_0067, g32p_row03_traceSegment_021_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 2970 270 = [0, 0, 0, 37] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2970 135 135, g32p_row03_traceSegment_021_2970_0135, g32p_row03_traceSegment_021_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_021 2700 540 = [0, 0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2700 270 270, g32p_row03_traceSegment_021_2700_0270, g32p_row03_traceSegment_021_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_021 2160 1080 = [0, 0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2160 540 540, g32p_row03_traceSegment_021_2160_0540, g32p_row03_traceSegment_021_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3256 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3264 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3256 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3256 8 9, g32p_row03_traceSegment_021_3256_0008, g32p_row03_traceSegment_021_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 3240 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3240 16 17, g32p_row03_traceSegment_021_3240_0016, g32p_row03_traceSegment_021_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3273 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3281 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3273 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3273 8 9, g32p_row03_traceSegment_021_3273_0008, g32p_row03_traceSegment_021_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3290 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3298 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3290 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3290 8 9, g32p_row03_traceSegment_021_3290_0008, g32p_row03_traceSegment_021_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3273 34 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3273 17 17, g32p_row03_traceSegment_021_3273_0017, g32p_row03_traceSegment_021_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 3240 67 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3240 33 34, g32p_row03_traceSegment_021_3240_0033, g32p_row03_traceSegment_021_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3307 8 9, g32p_row03_traceSegment_021_3307_0008, g32p_row03_traceSegment_021_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3324 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3324 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3324 8 9, g32p_row03_traceSegment_021_3324_0008, g32p_row03_traceSegment_021_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3307 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3307 17 17, g32p_row03_traceSegment_021_3307_0017, g32p_row03_traceSegment_021_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3341 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3349 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3341 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3341 8 9, g32p_row03_traceSegment_021_3341_0008, g32p_row03_traceSegment_021_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3358 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3358 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3358 8 9, g32p_row03_traceSegment_021_3358_0008, g32p_row03_traceSegment_021_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3341 34 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3341 17 17, g32p_row03_traceSegment_021_3341_0017, g32p_row03_traceSegment_021_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 3307 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3307 34 34, g32p_row03_traceSegment_021_3307_0034, g32p_row03_traceSegment_021_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 3240 135 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3240 67 68, g32p_row03_traceSegment_021_3240_0067, g32p_row03_traceSegment_021_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3391 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3391 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3391 8 9, g32p_row03_traceSegment_021_3391_0008, g32p_row03_traceSegment_021_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 3375 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3375 16 17, g32p_row03_traceSegment_021_3375_0016, g32p_row03_traceSegment_021_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3408 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3416 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3408 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3408 8 9, g32p_row03_traceSegment_021_3408_0008, g32p_row03_traceSegment_021_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3425 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3425 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3425 8 9, g32p_row03_traceSegment_021_3425_0008, g32p_row03_traceSegment_021_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3408 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3408 17 17, g32p_row03_traceSegment_021_3408_0017, g32p_row03_traceSegment_021_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 3375 67 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3375 33 34, g32p_row03_traceSegment_021_3375_0033, g32p_row03_traceSegment_021_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3442 8 9, g32p_row03_traceSegment_021_3442_0008, g32p_row03_traceSegment_021_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3467 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3459 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3459 8 9, g32p_row03_traceSegment_021_3459_0008, g32p_row03_traceSegment_021_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3442 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3442 17 17, g32p_row03_traceSegment_021_3442_0017, g32p_row03_traceSegment_021_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3476 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3484 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3476 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3476 8 9, g32p_row03_traceSegment_021_3476_0008, g32p_row03_traceSegment_021_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3501 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3493 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3493 8 9, g32p_row03_traceSegment_021_3493_0008, g32p_row03_traceSegment_021_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3476 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3476 17 17, g32p_row03_traceSegment_021_3476_0017, g32p_row03_traceSegment_021_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 3442 68 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3442 34 34, g32p_row03_traceSegment_021_3442_0034, g32p_row03_traceSegment_021_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 3375 135 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3375 67 68, g32p_row03_traceSegment_021_3375_0067, g32p_row03_traceSegment_021_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 3240 270 = [0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3240 135 135, g32p_row03_traceSegment_021_3240_0135, g32p_row03_traceSegment_021_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 3510 16 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3526 8 9, g32p_row03_traceSegment_021_3526_0008, g32p_row03_traceSegment_021_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 3510 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3510 16 17, g32p_row03_traceSegment_021_3510_0016, g32p_row03_traceSegment_021_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3551 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3543 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3543 8 9, g32p_row03_traceSegment_021_3543_0008, g32p_row03_traceSegment_021_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3560 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3560 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3560 8 9, g32p_row03_traceSegment_021_3560_0008, g32p_row03_traceSegment_021_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3543 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3543 17 17, g32p_row03_traceSegment_021_3543_0017, g32p_row03_traceSegment_021_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 3510 67 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3510 33 34, g32p_row03_traceSegment_021_3510_0033, g32p_row03_traceSegment_021_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3577 8 9, g32p_row03_traceSegment_021_3577_0008, g32p_row03_traceSegment_021_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3594 8 9, g32p_row03_traceSegment_021_3594_0008, g32p_row03_traceSegment_021_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3577 17 17, g32p_row03_traceSegment_021_3577_0017, g32p_row03_traceSegment_021_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3611 8 9, g32p_row03_traceSegment_021_3611_0008, g32p_row03_traceSegment_021_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3636 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3628 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3628 8 9, g32p_row03_traceSegment_021_3628_0008, g32p_row03_traceSegment_021_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3611 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3611 17 17, g32p_row03_traceSegment_021_3611_0017, g32p_row03_traceSegment_021_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 3577 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3577 34 34, g32p_row03_traceSegment_021_3577_0034, g32p_row03_traceSegment_021_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 3510 135 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3510 67 68, g32p_row03_traceSegment_021_3510_0067, g32p_row03_traceSegment_021_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 3645 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3661 8 9, g32p_row03_traceSegment_021_3661_0008, g32p_row03_traceSegment_021_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 3645 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3645 16 17, g32p_row03_traceSegment_021_3645_0016, g32p_row03_traceSegment_021_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3686 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3678 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3678 8 9, g32p_row03_traceSegment_021_3678_0008, g32p_row03_traceSegment_021_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3695 8 9, g32p_row03_traceSegment_021_3695_0008, g32p_row03_traceSegment_021_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3678 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3678 17 17, g32p_row03_traceSegment_021_3678_0017, g32p_row03_traceSegment_021_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 3645 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3645 33 34, g32p_row03_traceSegment_021_3645_0033, g32p_row03_traceSegment_021_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3720 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3712 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3712 8 9, g32p_row03_traceSegment_021_3712_0008, g32p_row03_traceSegment_021_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3729 8 9, g32p_row03_traceSegment_021_3729_0008, g32p_row03_traceSegment_021_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3712 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3712 17 17, g32p_row03_traceSegment_021_3712_0017, g32p_row03_traceSegment_021_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3746 8 9, g32p_row03_traceSegment_021_3746_0008, g32p_row03_traceSegment_021_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3763 8 9, g32p_row03_traceSegment_021_3763_0008, g32p_row03_traceSegment_021_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3746 17 17, g32p_row03_traceSegment_021_3746_0017, g32p_row03_traceSegment_021_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 3712 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3712 34 34, g32p_row03_traceSegment_021_3712_0034, g32p_row03_traceSegment_021_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 3645 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3645 67 68, g32p_row03_traceSegment_021_3645_0067, g32p_row03_traceSegment_021_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 3510 270 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3510 135 135, g32p_row03_traceSegment_021_3510_0135, g32p_row03_traceSegment_021_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_021 3240 540 = [0, 0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3240 270 270, g32p_row03_traceSegment_021_3240_0270, g32p_row03_traceSegment_021_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3796 8 9, g32p_row03_traceSegment_021_3796_0008, g32p_row03_traceSegment_021_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3780 16 17, g32p_row03_traceSegment_021_3780_0016, g32p_row03_traceSegment_021_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3813 8 9, g32p_row03_traceSegment_021_3813_0008, g32p_row03_traceSegment_021_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3830 8 9, g32p_row03_traceSegment_021_3830_0008, g32p_row03_traceSegment_021_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3813 17 17, g32p_row03_traceSegment_021_3813_0017, g32p_row03_traceSegment_021_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3780 33 34, g32p_row03_traceSegment_021_3780_0033, g32p_row03_traceSegment_021_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3847 8 9, g32p_row03_traceSegment_021_3847_0008, g32p_row03_traceSegment_021_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3864 8 9, g32p_row03_traceSegment_021_3864_0008, g32p_row03_traceSegment_021_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3847 17 17, g32p_row03_traceSegment_021_3847_0017, g32p_row03_traceSegment_021_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3881 8 9, g32p_row03_traceSegment_021_3881_0008, g32p_row03_traceSegment_021_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3898 8 9, g32p_row03_traceSegment_021_3898_0008, g32p_row03_traceSegment_021_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3881 17 17, g32p_row03_traceSegment_021_3881_0017, g32p_row03_traceSegment_021_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3847 34 34, g32p_row03_traceSegment_021_3847_0034, g32p_row03_traceSegment_021_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3780 67 68, g32p_row03_traceSegment_021_3780_0067, g32p_row03_traceSegment_021_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 3915 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3931 8 9, g32p_row03_traceSegment_021_3931_0008, g32p_row03_traceSegment_021_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 3915 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3915 16 17, g32p_row03_traceSegment_021_3915_0016, g32p_row03_traceSegment_021_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3948 8 9, g32p_row03_traceSegment_021_3948_0008, g32p_row03_traceSegment_021_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3965 8 9, g32p_row03_traceSegment_021_3965_0008, g32p_row03_traceSegment_021_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3948 17 17, g32p_row03_traceSegment_021_3948_0017, g32p_row03_traceSegment_021_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 3915 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3915 33 34, g32p_row03_traceSegment_021_3915_0033, g32p_row03_traceSegment_021_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3982 8 9, g32p_row03_traceSegment_021_3982_0008, g32p_row03_traceSegment_021_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4007 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 3999 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3999 8 9, g32p_row03_traceSegment_021_3999_0008, g32p_row03_traceSegment_021_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 3982 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3982 17 17, g32p_row03_traceSegment_021_3982_0017, g32p_row03_traceSegment_021_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4016 8 9, g32p_row03_traceSegment_021_4016_0008, g32p_row03_traceSegment_021_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4041 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4033 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4033 8 9, g32p_row03_traceSegment_021_4033_0008, g32p_row03_traceSegment_021_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 4016 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4016 17 17, g32p_row03_traceSegment_021_4016_0017, g32p_row03_traceSegment_021_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 3982 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3982 34 34, g32p_row03_traceSegment_021_3982_0034, g32p_row03_traceSegment_021_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 3915 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3915 67 68, g32p_row03_traceSegment_021_3915_0067, g32p_row03_traceSegment_021_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 3780 270 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3780 135 135, g32p_row03_traceSegment_021_3780_0135, g32p_row03_traceSegment_021_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4066 8 9, g32p_row03_traceSegment_021_4066_0008, g32p_row03_traceSegment_021_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4050 16 17, g32p_row03_traceSegment_021_4050_0016, g32p_row03_traceSegment_021_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4091 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4083 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4083 8 9, g32p_row03_traceSegment_021_4083_0008, g32p_row03_traceSegment_021_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4100 8 9, g32p_row03_traceSegment_021_4100_0008, g32p_row03_traceSegment_021_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 4083 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4083 17 17, g32p_row03_traceSegment_021_4083_0017, g32p_row03_traceSegment_021_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 4050 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4050 33 34, g32p_row03_traceSegment_021_4050_0033, g32p_row03_traceSegment_021_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4117 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4125 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4117 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4117 8 9, g32p_row03_traceSegment_021_4117_0008, g32p_row03_traceSegment_021_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4142 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4134 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4134 8 9, g32p_row03_traceSegment_021_4134_0008, g32p_row03_traceSegment_021_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 4117 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4117 17 17, g32p_row03_traceSegment_021_4117_0017, g32p_row03_traceSegment_021_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4151 8 9, g32p_row03_traceSegment_021_4151_0008, g32p_row03_traceSegment_021_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4168 8 9, g32p_row03_traceSegment_021_4168_0008, g32p_row03_traceSegment_021_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4151 17 17, g32p_row03_traceSegment_021_4151_0017, g32p_row03_traceSegment_021_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 4117 68 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4117 34 34, g32p_row03_traceSegment_021_4117_0034, g32p_row03_traceSegment_021_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 4050 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4050 67 68, g32p_row03_traceSegment_021_4050_0067, g32p_row03_traceSegment_021_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_021 4185 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4209 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4201 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4201 8 9, g32p_row03_traceSegment_021_4201_0008, g32p_row03_traceSegment_021_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_021 4185 33 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4185 16 17, g32p_row03_traceSegment_021_4185_0016, g32p_row03_traceSegment_021_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4226 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4218 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4218 8 9, g32p_row03_traceSegment_021_4218_0008, g32p_row03_traceSegment_021_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4235 8 9, g32p_row03_traceSegment_021_4235_0008, g32p_row03_traceSegment_021_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 4218 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4218 17 17, g32p_row03_traceSegment_021_4218_0017, g32p_row03_traceSegment_021_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_021 4185 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4185 33 34, g32p_row03_traceSegment_021_4185_0033, g32p_row03_traceSegment_021_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4252 8 9, g32p_row03_traceSegment_021_4252_0008, g32p_row03_traceSegment_021_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4269 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4269 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4269 8 9, g32p_row03_traceSegment_021_4269_0008, g32p_row03_traceSegment_021_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 4252 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4252 17 17, g32p_row03_traceSegment_021_4252_0017, g32p_row03_traceSegment_021_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4286 8 9, g32p_row03_traceSegment_021_4286_0008, g32p_row03_traceSegment_021_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_021 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_021 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_021_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_021 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4303 8 9, g32p_row03_traceSegment_021_4303_0008, g32p_row03_traceSegment_021_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_021 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4286 17 17, g32p_row03_traceSegment_021_4286_0017, g32p_row03_traceSegment_021_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_021 4252 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4252 34 34, g32p_row03_traceSegment_021_4252_0034, g32p_row03_traceSegment_021_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_021 4185 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4185 67 68, g32p_row03_traceSegment_021_4185_0067, g32p_row03_traceSegment_021_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_021_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_021 4050 270 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 4050 135 135, g32p_row03_traceSegment_021_4050_0135, g32p_row03_traceSegment_021_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_021 3780 540 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3780 270 270, g32p_row03_traceSegment_021_3780_0270, g32p_row03_traceSegment_021_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_021_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_021 3240 1080 = [0, 0, 0, 47] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 3240 540 540, g32p_row03_traceSegment_021_3240_0540, g32p_row03_traceSegment_021_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_021_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_021 2160 2160 = [0, 0, 0, 87] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 2160 1080 1080, g32p_row03_traceSegment_021_2160_1080, g32p_row03_traceSegment_021_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_021_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_021 0 4320 = [0, 0, 0, 240] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_021 0 2160 2160, g32p_row03_traceSegment_021_0000_2160, g32p_row03_traceSegment_021_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_021 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 21 = [0, 0, 0, 240] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_021_0000_4320

end HodgeLean.Foundations.Program

end
end
