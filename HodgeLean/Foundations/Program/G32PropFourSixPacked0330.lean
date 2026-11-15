import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_075 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 75 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_075_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 16 8 9, g32p_row03_traceSegment_075_0016_0008, g32p_row03_traceSegment_075_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 0 16 17, g32p_row03_traceSegment_075_0000_0016, g32p_row03_traceSegment_075_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 33 8 9, g32p_row03_traceSegment_075_0033_0008, g32p_row03_traceSegment_075_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 50 8 9, g32p_row03_traceSegment_075_0050_0008, g32p_row03_traceSegment_075_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 33 17 17, g32p_row03_traceSegment_075_0033_0017, g32p_row03_traceSegment_075_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 0 33 34, g32p_row03_traceSegment_075_0000_0033, g32p_row03_traceSegment_075_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 67 8 9, g32p_row03_traceSegment_075_0067_0008, g32p_row03_traceSegment_075_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 84 8 9, g32p_row03_traceSegment_075_0084_0008, g32p_row03_traceSegment_075_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 67 17 17, g32p_row03_traceSegment_075_0067_0017, g32p_row03_traceSegment_075_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 101 8 9, g32p_row03_traceSegment_075_0101_0008, g32p_row03_traceSegment_075_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 118 8 9, g32p_row03_traceSegment_075_0118_0008, g32p_row03_traceSegment_075_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 101 17 17, g32p_row03_traceSegment_075_0101_0017, g32p_row03_traceSegment_075_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 67 34 34, g32p_row03_traceSegment_075_0067_0034, g32p_row03_traceSegment_075_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 0 67 68, g32p_row03_traceSegment_075_0000_0067, g32p_row03_traceSegment_075_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 151 8 9, g32p_row03_traceSegment_075_0151_0008, g32p_row03_traceSegment_075_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 135 16 17, g32p_row03_traceSegment_075_0135_0016, g32p_row03_traceSegment_075_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 168 8 9, g32p_row03_traceSegment_075_0168_0008, g32p_row03_traceSegment_075_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 185 8 9, g32p_row03_traceSegment_075_0185_0008, g32p_row03_traceSegment_075_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 168 17 17, g32p_row03_traceSegment_075_0168_0017, g32p_row03_traceSegment_075_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 135 33 34, g32p_row03_traceSegment_075_0135_0033, g32p_row03_traceSegment_075_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 202 8 9, g32p_row03_traceSegment_075_0202_0008, g32p_row03_traceSegment_075_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 219 8 9, g32p_row03_traceSegment_075_0219_0008, g32p_row03_traceSegment_075_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 202 17 17, g32p_row03_traceSegment_075_0202_0017, g32p_row03_traceSegment_075_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 236 8 9, g32p_row03_traceSegment_075_0236_0008, g32p_row03_traceSegment_075_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 253 8 9, g32p_row03_traceSegment_075_0253_0008, g32p_row03_traceSegment_075_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 236 17 17, g32p_row03_traceSegment_075_0236_0017, g32p_row03_traceSegment_075_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 202 34 34, g32p_row03_traceSegment_075_0202_0034, g32p_row03_traceSegment_075_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 135 67 68, g32p_row03_traceSegment_075_0135_0067, g32p_row03_traceSegment_075_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 0 135 135, g32p_row03_traceSegment_075_0000_0135, g32p_row03_traceSegment_075_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 286 8 9, g32p_row03_traceSegment_075_0286_0008, g32p_row03_traceSegment_075_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 270 16 17, g32p_row03_traceSegment_075_0270_0016, g32p_row03_traceSegment_075_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 303 8 9, g32p_row03_traceSegment_075_0303_0008, g32p_row03_traceSegment_075_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 320 8 9, g32p_row03_traceSegment_075_0320_0008, g32p_row03_traceSegment_075_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 303 17 17, g32p_row03_traceSegment_075_0303_0017, g32p_row03_traceSegment_075_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 270 33 34, g32p_row03_traceSegment_075_0270_0033, g32p_row03_traceSegment_075_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 337 8 9, g32p_row03_traceSegment_075_0337_0008, g32p_row03_traceSegment_075_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 354 8 9, g32p_row03_traceSegment_075_0354_0008, g32p_row03_traceSegment_075_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 337 17 17, g32p_row03_traceSegment_075_0337_0017, g32p_row03_traceSegment_075_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 371 8 9, g32p_row03_traceSegment_075_0371_0008, g32p_row03_traceSegment_075_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 388 8 9, g32p_row03_traceSegment_075_0388_0008, g32p_row03_traceSegment_075_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 371 17 17, g32p_row03_traceSegment_075_0371_0017, g32p_row03_traceSegment_075_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 337 34 34, g32p_row03_traceSegment_075_0337_0034, g32p_row03_traceSegment_075_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 270 67 68, g32p_row03_traceSegment_075_0270_0067, g32p_row03_traceSegment_075_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 421 8 9, g32p_row03_traceSegment_075_0421_0008, g32p_row03_traceSegment_075_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 405 16 17, g32p_row03_traceSegment_075_0405_0016, g32p_row03_traceSegment_075_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 438 8 9, g32p_row03_traceSegment_075_0438_0008, g32p_row03_traceSegment_075_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 455 8 9, g32p_row03_traceSegment_075_0455_0008, g32p_row03_traceSegment_075_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 438 17 17, g32p_row03_traceSegment_075_0438_0017, g32p_row03_traceSegment_075_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 405 33 34, g32p_row03_traceSegment_075_0405_0033, g32p_row03_traceSegment_075_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 472 8 9, g32p_row03_traceSegment_075_0472_0008, g32p_row03_traceSegment_075_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 489 8 9, g32p_row03_traceSegment_075_0489_0008, g32p_row03_traceSegment_075_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 472 17 17, g32p_row03_traceSegment_075_0472_0017, g32p_row03_traceSegment_075_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 506 8 9, g32p_row03_traceSegment_075_0506_0008, g32p_row03_traceSegment_075_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 523 8 9, g32p_row03_traceSegment_075_0523_0008, g32p_row03_traceSegment_075_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 506 17 17, g32p_row03_traceSegment_075_0506_0017, g32p_row03_traceSegment_075_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 472 34 34, g32p_row03_traceSegment_075_0472_0034, g32p_row03_traceSegment_075_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 405 67 68, g32p_row03_traceSegment_075_0405_0067, g32p_row03_traceSegment_075_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 270 135 135, g32p_row03_traceSegment_075_0270_0135, g32p_row03_traceSegment_075_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_075 0 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 0 270 270, g32p_row03_traceSegment_075_0000_0270, g32p_row03_traceSegment_075_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 556 8 9, g32p_row03_traceSegment_075_0556_0008, g32p_row03_traceSegment_075_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 540 16 17, g32p_row03_traceSegment_075_0540_0016, g32p_row03_traceSegment_075_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 573 8 9, g32p_row03_traceSegment_075_0573_0008, g32p_row03_traceSegment_075_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 590 8 9, g32p_row03_traceSegment_075_0590_0008, g32p_row03_traceSegment_075_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 573 17 17, g32p_row03_traceSegment_075_0573_0017, g32p_row03_traceSegment_075_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 540 33 34, g32p_row03_traceSegment_075_0540_0033, g32p_row03_traceSegment_075_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 607 8 9, g32p_row03_traceSegment_075_0607_0008, g32p_row03_traceSegment_075_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 624 8 9, g32p_row03_traceSegment_075_0624_0008, g32p_row03_traceSegment_075_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 607 17 17, g32p_row03_traceSegment_075_0607_0017, g32p_row03_traceSegment_075_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 641 8 9, g32p_row03_traceSegment_075_0641_0008, g32p_row03_traceSegment_075_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 658 8 9, g32p_row03_traceSegment_075_0658_0008, g32p_row03_traceSegment_075_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 641 17 17, g32p_row03_traceSegment_075_0641_0017, g32p_row03_traceSegment_075_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 607 34 34, g32p_row03_traceSegment_075_0607_0034, g32p_row03_traceSegment_075_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 540 67 68, g32p_row03_traceSegment_075_0540_0067, g32p_row03_traceSegment_075_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 691 8 9, g32p_row03_traceSegment_075_0691_0008, g32p_row03_traceSegment_075_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 675 16 17, g32p_row03_traceSegment_075_0675_0016, g32p_row03_traceSegment_075_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 708 8 9, g32p_row03_traceSegment_075_0708_0008, g32p_row03_traceSegment_075_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 725 8 9, g32p_row03_traceSegment_075_0725_0008, g32p_row03_traceSegment_075_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 708 17 17, g32p_row03_traceSegment_075_0708_0017, g32p_row03_traceSegment_075_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 675 33 34, g32p_row03_traceSegment_075_0675_0033, g32p_row03_traceSegment_075_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 742 8 9, g32p_row03_traceSegment_075_0742_0008, g32p_row03_traceSegment_075_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 759 8 9, g32p_row03_traceSegment_075_0759_0008, g32p_row03_traceSegment_075_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 742 17 17, g32p_row03_traceSegment_075_0742_0017, g32p_row03_traceSegment_075_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 776 8 9, g32p_row03_traceSegment_075_0776_0008, g32p_row03_traceSegment_075_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 793 8 9, g32p_row03_traceSegment_075_0793_0008, g32p_row03_traceSegment_075_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 776 17 17, g32p_row03_traceSegment_075_0776_0017, g32p_row03_traceSegment_075_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 742 34 34, g32p_row03_traceSegment_075_0742_0034, g32p_row03_traceSegment_075_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 675 67 68, g32p_row03_traceSegment_075_0675_0067, g32p_row03_traceSegment_075_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 540 135 135, g32p_row03_traceSegment_075_0540_0135, g32p_row03_traceSegment_075_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 826 8 9, g32p_row03_traceSegment_075_0826_0008, g32p_row03_traceSegment_075_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 810 16 17, g32p_row03_traceSegment_075_0810_0016, g32p_row03_traceSegment_075_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 843 8 9, g32p_row03_traceSegment_075_0843_0008, g32p_row03_traceSegment_075_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 860 8 9, g32p_row03_traceSegment_075_0860_0008, g32p_row03_traceSegment_075_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 843 17 17, g32p_row03_traceSegment_075_0843_0017, g32p_row03_traceSegment_075_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 810 33 34, g32p_row03_traceSegment_075_0810_0033, g32p_row03_traceSegment_075_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 877 8 9, g32p_row03_traceSegment_075_0877_0008, g32p_row03_traceSegment_075_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 894 8 9, g32p_row03_traceSegment_075_0894_0008, g32p_row03_traceSegment_075_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 877 17 17, g32p_row03_traceSegment_075_0877_0017, g32p_row03_traceSegment_075_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 911 8 9, g32p_row03_traceSegment_075_0911_0008, g32p_row03_traceSegment_075_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 928 8 9, g32p_row03_traceSegment_075_0928_0008, g32p_row03_traceSegment_075_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 911 17 17, g32p_row03_traceSegment_075_0911_0017, g32p_row03_traceSegment_075_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 877 34 34, g32p_row03_traceSegment_075_0877_0034, g32p_row03_traceSegment_075_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 810 67 68, g32p_row03_traceSegment_075_0810_0067, g32p_row03_traceSegment_075_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 961 8 9, g32p_row03_traceSegment_075_0961_0008, g32p_row03_traceSegment_075_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 945 16 17, g32p_row03_traceSegment_075_0945_0016, g32p_row03_traceSegment_075_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 978 8 9, g32p_row03_traceSegment_075_0978_0008, g32p_row03_traceSegment_075_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 995 8 9, g32p_row03_traceSegment_075_0995_0008, g32p_row03_traceSegment_075_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 978 17 17, g32p_row03_traceSegment_075_0978_0017, g32p_row03_traceSegment_075_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 945 33 34, g32p_row03_traceSegment_075_0945_0033, g32p_row03_traceSegment_075_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1012 8 9, g32p_row03_traceSegment_075_1012_0008, g32p_row03_traceSegment_075_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1029 8 9, g32p_row03_traceSegment_075_1029_0008, g32p_row03_traceSegment_075_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1012 17 17, g32p_row03_traceSegment_075_1012_0017, g32p_row03_traceSegment_075_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1046 8 9, g32p_row03_traceSegment_075_1046_0008, g32p_row03_traceSegment_075_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1063 8 9, g32p_row03_traceSegment_075_1063_0008, g32p_row03_traceSegment_075_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1046 17 17, g32p_row03_traceSegment_075_1046_0017, g32p_row03_traceSegment_075_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1012 34 34, g32p_row03_traceSegment_075_1012_0034, g32p_row03_traceSegment_075_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 945 67 68, g32p_row03_traceSegment_075_0945_0067, g32p_row03_traceSegment_075_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 810 135 135, g32p_row03_traceSegment_075_0810_0135, g32p_row03_traceSegment_075_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_075 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 540 270 270, g32p_row03_traceSegment_075_0540_0270, g32p_row03_traceSegment_075_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_075 0 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 0 540 540, g32p_row03_traceSegment_075_0000_0540, g32p_row03_traceSegment_075_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1096 8 9, g32p_row03_traceSegment_075_1096_0008, g32p_row03_traceSegment_075_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1080 16 17, g32p_row03_traceSegment_075_1080_0016, g32p_row03_traceSegment_075_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1113 8 9, g32p_row03_traceSegment_075_1113_0008, g32p_row03_traceSegment_075_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1130 8 9, g32p_row03_traceSegment_075_1130_0008, g32p_row03_traceSegment_075_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1113 17 17, g32p_row03_traceSegment_075_1113_0017, g32p_row03_traceSegment_075_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1080 33 34, g32p_row03_traceSegment_075_1080_0033, g32p_row03_traceSegment_075_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1147 8 9, g32p_row03_traceSegment_075_1147_0008, g32p_row03_traceSegment_075_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1164 8 9, g32p_row03_traceSegment_075_1164_0008, g32p_row03_traceSegment_075_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1147 17 17, g32p_row03_traceSegment_075_1147_0017, g32p_row03_traceSegment_075_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1181 8 9, g32p_row03_traceSegment_075_1181_0008, g32p_row03_traceSegment_075_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1198 8 9, g32p_row03_traceSegment_075_1198_0008, g32p_row03_traceSegment_075_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1181 17 17, g32p_row03_traceSegment_075_1181_0017, g32p_row03_traceSegment_075_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1147 34 34, g32p_row03_traceSegment_075_1147_0034, g32p_row03_traceSegment_075_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1080 67 68, g32p_row03_traceSegment_075_1080_0067, g32p_row03_traceSegment_075_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1231 8 9, g32p_row03_traceSegment_075_1231_0008, g32p_row03_traceSegment_075_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1215 16 17, g32p_row03_traceSegment_075_1215_0016, g32p_row03_traceSegment_075_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1248 8 9, g32p_row03_traceSegment_075_1248_0008, g32p_row03_traceSegment_075_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1265 8 9, g32p_row03_traceSegment_075_1265_0008, g32p_row03_traceSegment_075_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1248 17 17, g32p_row03_traceSegment_075_1248_0017, g32p_row03_traceSegment_075_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1215 33 34, g32p_row03_traceSegment_075_1215_0033, g32p_row03_traceSegment_075_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1282 8 9, g32p_row03_traceSegment_075_1282_0008, g32p_row03_traceSegment_075_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1299 8 9, g32p_row03_traceSegment_075_1299_0008, g32p_row03_traceSegment_075_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1282 17 17, g32p_row03_traceSegment_075_1282_0017, g32p_row03_traceSegment_075_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1316 8 9, g32p_row03_traceSegment_075_1316_0008, g32p_row03_traceSegment_075_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1333 8 9, g32p_row03_traceSegment_075_1333_0008, g32p_row03_traceSegment_075_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1316 17 17, g32p_row03_traceSegment_075_1316_0017, g32p_row03_traceSegment_075_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1282 34 34, g32p_row03_traceSegment_075_1282_0034, g32p_row03_traceSegment_075_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1215 67 68, g32p_row03_traceSegment_075_1215_0067, g32p_row03_traceSegment_075_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1080 135 135, g32p_row03_traceSegment_075_1080_0135, g32p_row03_traceSegment_075_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1366 8 9, g32p_row03_traceSegment_075_1366_0008, g32p_row03_traceSegment_075_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1350 16 17, g32p_row03_traceSegment_075_1350_0016, g32p_row03_traceSegment_075_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1383 8 9, g32p_row03_traceSegment_075_1383_0008, g32p_row03_traceSegment_075_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1400 8 9, g32p_row03_traceSegment_075_1400_0008, g32p_row03_traceSegment_075_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1383 17 17, g32p_row03_traceSegment_075_1383_0017, g32p_row03_traceSegment_075_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1350 33 34, g32p_row03_traceSegment_075_1350_0033, g32p_row03_traceSegment_075_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1417 8 9, g32p_row03_traceSegment_075_1417_0008, g32p_row03_traceSegment_075_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1434 8 9, g32p_row03_traceSegment_075_1434_0008, g32p_row03_traceSegment_075_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1417 17 17, g32p_row03_traceSegment_075_1417_0017, g32p_row03_traceSegment_075_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1451 8 9, g32p_row03_traceSegment_075_1451_0008, g32p_row03_traceSegment_075_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1468 8 9, g32p_row03_traceSegment_075_1468_0008, g32p_row03_traceSegment_075_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1451 17 17, g32p_row03_traceSegment_075_1451_0017, g32p_row03_traceSegment_075_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1417 34 34, g32p_row03_traceSegment_075_1417_0034, g32p_row03_traceSegment_075_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1350 67 68, g32p_row03_traceSegment_075_1350_0067, g32p_row03_traceSegment_075_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1501 8 9, g32p_row03_traceSegment_075_1501_0008, g32p_row03_traceSegment_075_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1485 16 17, g32p_row03_traceSegment_075_1485_0016, g32p_row03_traceSegment_075_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1518 8 9, g32p_row03_traceSegment_075_1518_0008, g32p_row03_traceSegment_075_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1535 8 9, g32p_row03_traceSegment_075_1535_0008, g32p_row03_traceSegment_075_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1518 17 17, g32p_row03_traceSegment_075_1518_0017, g32p_row03_traceSegment_075_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1485 33 34, g32p_row03_traceSegment_075_1485_0033, g32p_row03_traceSegment_075_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1552 8 9, g32p_row03_traceSegment_075_1552_0008, g32p_row03_traceSegment_075_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1569 8 9, g32p_row03_traceSegment_075_1569_0008, g32p_row03_traceSegment_075_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1552 17 17, g32p_row03_traceSegment_075_1552_0017, g32p_row03_traceSegment_075_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1586 8 9, g32p_row03_traceSegment_075_1586_0008, g32p_row03_traceSegment_075_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1603 8 9, g32p_row03_traceSegment_075_1603_0008, g32p_row03_traceSegment_075_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1586 17 17, g32p_row03_traceSegment_075_1586_0017, g32p_row03_traceSegment_075_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1552 34 34, g32p_row03_traceSegment_075_1552_0034, g32p_row03_traceSegment_075_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1485 67 68, g32p_row03_traceSegment_075_1485_0067, g32p_row03_traceSegment_075_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1350 135 135, g32p_row03_traceSegment_075_1350_0135, g32p_row03_traceSegment_075_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_075 1080 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1080 270 270, g32p_row03_traceSegment_075_1080_0270, g32p_row03_traceSegment_075_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1636 8 9, g32p_row03_traceSegment_075_1636_0008, g32p_row03_traceSegment_075_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1620 16 17, g32p_row03_traceSegment_075_1620_0016, g32p_row03_traceSegment_075_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1653 8 9, g32p_row03_traceSegment_075_1653_0008, g32p_row03_traceSegment_075_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1670 8 9, g32p_row03_traceSegment_075_1670_0008, g32p_row03_traceSegment_075_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1653 17 17, g32p_row03_traceSegment_075_1653_0017, g32p_row03_traceSegment_075_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1620 33 34, g32p_row03_traceSegment_075_1620_0033, g32p_row03_traceSegment_075_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1687 8 9, g32p_row03_traceSegment_075_1687_0008, g32p_row03_traceSegment_075_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1704 8 9, g32p_row03_traceSegment_075_1704_0008, g32p_row03_traceSegment_075_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1687 17 17, g32p_row03_traceSegment_075_1687_0017, g32p_row03_traceSegment_075_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1721 8 9, g32p_row03_traceSegment_075_1721_0008, g32p_row03_traceSegment_075_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1738 8 9, g32p_row03_traceSegment_075_1738_0008, g32p_row03_traceSegment_075_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1721 17 17, g32p_row03_traceSegment_075_1721_0017, g32p_row03_traceSegment_075_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1687 34 34, g32p_row03_traceSegment_075_1687_0034, g32p_row03_traceSegment_075_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1620 67 68, g32p_row03_traceSegment_075_1620_0067, g32p_row03_traceSegment_075_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1771 8 9, g32p_row03_traceSegment_075_1771_0008, g32p_row03_traceSegment_075_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1755 16 17, g32p_row03_traceSegment_075_1755_0016, g32p_row03_traceSegment_075_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1788 8 9, g32p_row03_traceSegment_075_1788_0008, g32p_row03_traceSegment_075_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1805 8 9, g32p_row03_traceSegment_075_1805_0008, g32p_row03_traceSegment_075_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1788 17 17, g32p_row03_traceSegment_075_1788_0017, g32p_row03_traceSegment_075_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1755 33 34, g32p_row03_traceSegment_075_1755_0033, g32p_row03_traceSegment_075_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1822 8 9, g32p_row03_traceSegment_075_1822_0008, g32p_row03_traceSegment_075_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1839 8 9, g32p_row03_traceSegment_075_1839_0008, g32p_row03_traceSegment_075_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1822 17 17, g32p_row03_traceSegment_075_1822_0017, g32p_row03_traceSegment_075_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1856 8 9, g32p_row03_traceSegment_075_1856_0008, g32p_row03_traceSegment_075_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1873 8 9, g32p_row03_traceSegment_075_1873_0008, g32p_row03_traceSegment_075_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1856 17 17, g32p_row03_traceSegment_075_1856_0017, g32p_row03_traceSegment_075_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1822 34 34, g32p_row03_traceSegment_075_1822_0034, g32p_row03_traceSegment_075_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1755 67 68, g32p_row03_traceSegment_075_1755_0067, g32p_row03_traceSegment_075_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1620 135 135, g32p_row03_traceSegment_075_1620_0135, g32p_row03_traceSegment_075_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1906 8 9, g32p_row03_traceSegment_075_1906_0008, g32p_row03_traceSegment_075_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1890 16 17, g32p_row03_traceSegment_075_1890_0016, g32p_row03_traceSegment_075_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1923 8 9, g32p_row03_traceSegment_075_1923_0008, g32p_row03_traceSegment_075_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1940 8 9, g32p_row03_traceSegment_075_1940_0008, g32p_row03_traceSegment_075_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1923 17 17, g32p_row03_traceSegment_075_1923_0017, g32p_row03_traceSegment_075_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1890 33 34, g32p_row03_traceSegment_075_1890_0033, g32p_row03_traceSegment_075_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1957 8 9, g32p_row03_traceSegment_075_1957_0008, g32p_row03_traceSegment_075_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1974 8 9, g32p_row03_traceSegment_075_1974_0008, g32p_row03_traceSegment_075_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1957 17 17, g32p_row03_traceSegment_075_1957_0017, g32p_row03_traceSegment_075_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1991 8 9, g32p_row03_traceSegment_075_1991_0008, g32p_row03_traceSegment_075_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2008 8 9, g32p_row03_traceSegment_075_2008_0008, g32p_row03_traceSegment_075_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1991 17 17, g32p_row03_traceSegment_075_1991_0017, g32p_row03_traceSegment_075_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1957 34 34, g32p_row03_traceSegment_075_1957_0034, g32p_row03_traceSegment_075_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1890 67 68, g32p_row03_traceSegment_075_1890_0067, g32p_row03_traceSegment_075_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2049 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2041 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2041 8 9, g32p_row03_traceSegment_075_2041_0008, g32p_row03_traceSegment_075_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 2025 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2025 16 17, g32p_row03_traceSegment_075_2025_0016, g32p_row03_traceSegment_075_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2066 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2058 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2058 8 9, g32p_row03_traceSegment_075_2058_0008, g32p_row03_traceSegment_075_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2083 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2075 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2075 8 9, g32p_row03_traceSegment_075_2075_0008, g32p_row03_traceSegment_075_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2058 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2058 17 17, g32p_row03_traceSegment_075_2058_0017, g32p_row03_traceSegment_075_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 2025 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2025 33 34, g32p_row03_traceSegment_075_2025_0033, g32p_row03_traceSegment_075_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2092 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2100 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2092 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2092 8 9, g32p_row03_traceSegment_075_2092_0008, g32p_row03_traceSegment_075_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2109 8 9, g32p_row03_traceSegment_075_2109_0008, g32p_row03_traceSegment_075_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2092 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2092 17 17, g32p_row03_traceSegment_075_2092_0017, g32p_row03_traceSegment_075_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2134 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2126 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2126 8 9, g32p_row03_traceSegment_075_2126_0008, g32p_row03_traceSegment_075_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2143 8 9, g32p_row03_traceSegment_075_2143_0008, g32p_row03_traceSegment_075_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2126 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2126 17 17, g32p_row03_traceSegment_075_2126_0017, g32p_row03_traceSegment_075_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 2092 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2092 34 34, g32p_row03_traceSegment_075_2092_0034, g32p_row03_traceSegment_075_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 2025 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2025 67 68, g32p_row03_traceSegment_075_2025_0067, g32p_row03_traceSegment_075_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 1890 270 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1890 135 135, g32p_row03_traceSegment_075_1890_0135, g32p_row03_traceSegment_075_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_075 1620 540 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1620 270 270, g32p_row03_traceSegment_075_1620_0270, g32p_row03_traceSegment_075_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_075_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_075 1080 1080 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 1080 540 540, g32p_row03_traceSegment_075_1080_0540, g32p_row03_traceSegment_075_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_075 0 2160 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 0 1080 1080, g32p_row03_traceSegment_075_0000_1080, g32p_row03_traceSegment_075_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 2160 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2176 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2184 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2176 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2176 8 9, g32p_row03_traceSegment_075_2176_0008, g32p_row03_traceSegment_075_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 2160 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2160 16 17, g32p_row03_traceSegment_075_2160_0016, g32p_row03_traceSegment_075_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2201 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2193 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2193 8 9, g32p_row03_traceSegment_075_2193_0008, g32p_row03_traceSegment_075_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2210 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2210 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2210 8 9, g32p_row03_traceSegment_075_2210_0008, g32p_row03_traceSegment_075_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2193 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2193 17 17, g32p_row03_traceSegment_075_2193_0017, g32p_row03_traceSegment_075_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 2160 67 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2160 33 34, g32p_row03_traceSegment_075_2160_0033, g32p_row03_traceSegment_075_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2227 8 9, g32p_row03_traceSegment_075_2227_0008, g32p_row03_traceSegment_075_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2252 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2244 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2244 8 9, g32p_row03_traceSegment_075_2244_0008, g32p_row03_traceSegment_075_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2227 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2227 17 17, g32p_row03_traceSegment_075_2227_0017, g32p_row03_traceSegment_075_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2269 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2261 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2261 8 9, g32p_row03_traceSegment_075_2261_0008, g32p_row03_traceSegment_075_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2278 8 9, g32p_row03_traceSegment_075_2278_0008, g32p_row03_traceSegment_075_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2261 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2261 17 17, g32p_row03_traceSegment_075_2261_0017, g32p_row03_traceSegment_075_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 2227 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2227 34 34, g32p_row03_traceSegment_075_2227_0034, g32p_row03_traceSegment_075_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 2160 135 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2160 67 68, g32p_row03_traceSegment_075_2160_0067, g32p_row03_traceSegment_075_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 2295 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2311 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2319 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2311 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2311 8 9, g32p_row03_traceSegment_075_2311_0008, g32p_row03_traceSegment_075_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 2295 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2295 16 17, g32p_row03_traceSegment_075_2295_0016, g32p_row03_traceSegment_075_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2328 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2328 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2328 8 9, g32p_row03_traceSegment_075_2328_0008, g32p_row03_traceSegment_075_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2345 8 9, g32p_row03_traceSegment_075_2345_0008, g32p_row03_traceSegment_075_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2328 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2328 17 17, g32p_row03_traceSegment_075_2328_0017, g32p_row03_traceSegment_075_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 2295 67 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2295 33 34, g32p_row03_traceSegment_075_2295_0033, g32p_row03_traceSegment_075_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2370 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2362 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2362 8 9, g32p_row03_traceSegment_075_2362_0008, g32p_row03_traceSegment_075_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2387 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2379 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2379 8 9, g32p_row03_traceSegment_075_2379_0008, g32p_row03_traceSegment_075_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2362 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2362 17 17, g32p_row03_traceSegment_075_2362_0017, g32p_row03_traceSegment_075_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2396 8 9, g32p_row03_traceSegment_075_2396_0008, g32p_row03_traceSegment_075_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2413 8 9, g32p_row03_traceSegment_075_2413_0008, g32p_row03_traceSegment_075_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2396 17 17, g32p_row03_traceSegment_075_2396_0017, g32p_row03_traceSegment_075_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 2362 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2362 34 34, g32p_row03_traceSegment_075_2362_0034, g32p_row03_traceSegment_075_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 2295 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2295 67 68, g32p_row03_traceSegment_075_2295_0067, g32p_row03_traceSegment_075_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 2160 270 = [13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2160 135 135, g32p_row03_traceSegment_075_2160_0135, g32p_row03_traceSegment_075_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2454 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2446 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2446 8 9, g32p_row03_traceSegment_075_2446_0008, g32p_row03_traceSegment_075_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 2430 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2430 16 17, g32p_row03_traceSegment_075_2430_0016, g32p_row03_traceSegment_075_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2463 8 9, g32p_row03_traceSegment_075_2463_0008, g32p_row03_traceSegment_075_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2488 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2480 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2480 8 9, g32p_row03_traceSegment_075_2480_0008, g32p_row03_traceSegment_075_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2463 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2463 17 17, g32p_row03_traceSegment_075_2463_0017, g32p_row03_traceSegment_075_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 2430 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2430 33 34, g32p_row03_traceSegment_075_2430_0033, g32p_row03_traceSegment_075_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2497 8 9, g32p_row03_traceSegment_075_2497_0008, g32p_row03_traceSegment_075_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2514 8 9, g32p_row03_traceSegment_075_2514_0008, g32p_row03_traceSegment_075_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2497 17 17, g32p_row03_traceSegment_075_2497_0017, g32p_row03_traceSegment_075_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2531 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2539 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2531 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2531 8 9, g32p_row03_traceSegment_075_2531_0008, g32p_row03_traceSegment_075_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2548 8 9, g32p_row03_traceSegment_075_2548_0008, g32p_row03_traceSegment_075_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2531 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2531 17 17, g32p_row03_traceSegment_075_2531_0017, g32p_row03_traceSegment_075_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 2497 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2497 34 34, g32p_row03_traceSegment_075_2497_0034, g32p_row03_traceSegment_075_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 2430 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2430 67 68, g32p_row03_traceSegment_075_2430_0067, g32p_row03_traceSegment_075_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 2565 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2581 8 9, g32p_row03_traceSegment_075_2581_0008, g32p_row03_traceSegment_075_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 2565 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2565 16 17, g32p_row03_traceSegment_075_2565_0016, g32p_row03_traceSegment_075_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2598 8 9, g32p_row03_traceSegment_075_2598_0008, g32p_row03_traceSegment_075_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2615 8 9, g32p_row03_traceSegment_075_2615_0008, g32p_row03_traceSegment_075_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2598 17 17, g32p_row03_traceSegment_075_2598_0017, g32p_row03_traceSegment_075_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 2565 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2565 33 34, g32p_row03_traceSegment_075_2565_0033, g32p_row03_traceSegment_075_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2632 8 9, g32p_row03_traceSegment_075_2632_0008, g32p_row03_traceSegment_075_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2649 8 9, g32p_row03_traceSegment_075_2649_0008, g32p_row03_traceSegment_075_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2632 17 17, g32p_row03_traceSegment_075_2632_0017, g32p_row03_traceSegment_075_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2666 8 9, g32p_row03_traceSegment_075_2666_0008, g32p_row03_traceSegment_075_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2683 8 9, g32p_row03_traceSegment_075_2683_0008, g32p_row03_traceSegment_075_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2666 17 17, g32p_row03_traceSegment_075_2666_0017, g32p_row03_traceSegment_075_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2632 34 34, g32p_row03_traceSegment_075_2632_0034, g32p_row03_traceSegment_075_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 2565 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2565 67 68, g32p_row03_traceSegment_075_2565_0067, g32p_row03_traceSegment_075_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 2430 270 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2430 135 135, g32p_row03_traceSegment_075_2430_0135, g32p_row03_traceSegment_075_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_075 2160 540 = [18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2160 270 270, g32p_row03_traceSegment_075_2160_0270, g32p_row03_traceSegment_075_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2716 8 9, g32p_row03_traceSegment_075_2716_0008, g32p_row03_traceSegment_075_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2700 16 17, g32p_row03_traceSegment_075_2700_0016, g32p_row03_traceSegment_075_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2733 8 9, g32p_row03_traceSegment_075_2733_0008, g32p_row03_traceSegment_075_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2750 8 9, g32p_row03_traceSegment_075_2750_0008, g32p_row03_traceSegment_075_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2733 17 17, g32p_row03_traceSegment_075_2733_0017, g32p_row03_traceSegment_075_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2700 33 34, g32p_row03_traceSegment_075_2700_0033, g32p_row03_traceSegment_075_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2775 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2767 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2767 8 9, g32p_row03_traceSegment_075_2767_0008, g32p_row03_traceSegment_075_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2784 8 9, g32p_row03_traceSegment_075_2784_0008, g32p_row03_traceSegment_075_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2767 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2767 17 17, g32p_row03_traceSegment_075_2767_0017, g32p_row03_traceSegment_075_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2801 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2801 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2801 8 9, g32p_row03_traceSegment_075_2801_0008, g32p_row03_traceSegment_075_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2826 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2818 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2818 8 9, g32p_row03_traceSegment_075_2818_0008, g32p_row03_traceSegment_075_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2801 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2801 17 17, g32p_row03_traceSegment_075_2801_0017, g32p_row03_traceSegment_075_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 2767 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2767 34 34, g32p_row03_traceSegment_075_2767_0034, g32p_row03_traceSegment_075_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 2700 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2700 67 68, g32p_row03_traceSegment_075_2700_0067, g32p_row03_traceSegment_075_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2851 8 9, g32p_row03_traceSegment_075_2851_0008, g32p_row03_traceSegment_075_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2835 16 17, g32p_row03_traceSegment_075_2835_0016, g32p_row03_traceSegment_075_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2876 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2868 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2868 8 9, g32p_row03_traceSegment_075_2868_0008, g32p_row03_traceSegment_075_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2885 8 9, g32p_row03_traceSegment_075_2885_0008, g32p_row03_traceSegment_075_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2868 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2868 17 17, g32p_row03_traceSegment_075_2868_0017, g32p_row03_traceSegment_075_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 2835 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2835 33 34, g32p_row03_traceSegment_075_2835_0033, g32p_row03_traceSegment_075_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2902 8 9, g32p_row03_traceSegment_075_2902_0008, g32p_row03_traceSegment_075_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2919 8 9, g32p_row03_traceSegment_075_2919_0008, g32p_row03_traceSegment_075_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2902 17 17, g32p_row03_traceSegment_075_2902_0017, g32p_row03_traceSegment_075_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2936 8 9, g32p_row03_traceSegment_075_2936_0008, g32p_row03_traceSegment_075_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2953 8 9, g32p_row03_traceSegment_075_2953_0008, g32p_row03_traceSegment_075_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2936 17 17, g32p_row03_traceSegment_075_2936_0017, g32p_row03_traceSegment_075_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2902 34 34, g32p_row03_traceSegment_075_2902_0034, g32p_row03_traceSegment_075_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 2835 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2835 67 68, g32p_row03_traceSegment_075_2835_0067, g32p_row03_traceSegment_075_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 2700 270 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2700 135 135, g32p_row03_traceSegment_075_2700_0135, g32p_row03_traceSegment_075_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2986 8 9, g32p_row03_traceSegment_075_2986_0008, g32p_row03_traceSegment_075_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2970 16 17, g32p_row03_traceSegment_075_2970_0016, g32p_row03_traceSegment_075_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3003 8 9, g32p_row03_traceSegment_075_3003_0008, g32p_row03_traceSegment_075_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3020 8 9, g32p_row03_traceSegment_075_3020_0008, g32p_row03_traceSegment_075_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3003 17 17, g32p_row03_traceSegment_075_3003_0017, g32p_row03_traceSegment_075_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2970 33 34, g32p_row03_traceSegment_075_2970_0033, g32p_row03_traceSegment_075_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3037 8 9, g32p_row03_traceSegment_075_3037_0008, g32p_row03_traceSegment_075_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3054 8 9, g32p_row03_traceSegment_075_3054_0008, g32p_row03_traceSegment_075_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3037 17 17, g32p_row03_traceSegment_075_3037_0017, g32p_row03_traceSegment_075_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3071 8 9, g32p_row03_traceSegment_075_3071_0008, g32p_row03_traceSegment_075_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3088 8 9, g32p_row03_traceSegment_075_3088_0008, g32p_row03_traceSegment_075_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3071 17 17, g32p_row03_traceSegment_075_3071_0017, g32p_row03_traceSegment_075_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3037 34 34, g32p_row03_traceSegment_075_3037_0034, g32p_row03_traceSegment_075_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2970 67 68, g32p_row03_traceSegment_075_2970_0067, g32p_row03_traceSegment_075_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3121 8 9, g32p_row03_traceSegment_075_3121_0008, g32p_row03_traceSegment_075_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3105 16 17, g32p_row03_traceSegment_075_3105_0016, g32p_row03_traceSegment_075_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3138 8 9, g32p_row03_traceSegment_075_3138_0008, g32p_row03_traceSegment_075_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3155 8 9, g32p_row03_traceSegment_075_3155_0008, g32p_row03_traceSegment_075_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3138 17 17, g32p_row03_traceSegment_075_3138_0017, g32p_row03_traceSegment_075_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3105 33 34, g32p_row03_traceSegment_075_3105_0033, g32p_row03_traceSegment_075_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3172 8 9, g32p_row03_traceSegment_075_3172_0008, g32p_row03_traceSegment_075_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3189 8 9, g32p_row03_traceSegment_075_3189_0008, g32p_row03_traceSegment_075_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3172 17 17, g32p_row03_traceSegment_075_3172_0017, g32p_row03_traceSegment_075_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3206 8 9, g32p_row03_traceSegment_075_3206_0008, g32p_row03_traceSegment_075_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3223 8 9, g32p_row03_traceSegment_075_3223_0008, g32p_row03_traceSegment_075_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3206 17 17, g32p_row03_traceSegment_075_3206_0017, g32p_row03_traceSegment_075_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3172 34 34, g32p_row03_traceSegment_075_3172_0034, g32p_row03_traceSegment_075_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3105 67 68, g32p_row03_traceSegment_075_3105_0067, g32p_row03_traceSegment_075_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2970 135 135, g32p_row03_traceSegment_075_2970_0135, g32p_row03_traceSegment_075_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_075 2700 540 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2700 270 270, g32p_row03_traceSegment_075_2700_0270, g32p_row03_traceSegment_075_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_075 2160 1080 = [22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2160 540 540, g32p_row03_traceSegment_075_2160_0540, g32p_row03_traceSegment_075_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3256 8 9, g32p_row03_traceSegment_075_3256_0008, g32p_row03_traceSegment_075_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3240 16 17, g32p_row03_traceSegment_075_3240_0016, g32p_row03_traceSegment_075_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3273 8 9, g32p_row03_traceSegment_075_3273_0008, g32p_row03_traceSegment_075_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3290 8 9, g32p_row03_traceSegment_075_3290_0008, g32p_row03_traceSegment_075_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3273 17 17, g32p_row03_traceSegment_075_3273_0017, g32p_row03_traceSegment_075_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3240 33 34, g32p_row03_traceSegment_075_3240_0033, g32p_row03_traceSegment_075_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3307 8 9, g32p_row03_traceSegment_075_3307_0008, g32p_row03_traceSegment_075_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3324 8 9, g32p_row03_traceSegment_075_3324_0008, g32p_row03_traceSegment_075_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3307 17 17, g32p_row03_traceSegment_075_3307_0017, g32p_row03_traceSegment_075_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3341 8 9, g32p_row03_traceSegment_075_3341_0008, g32p_row03_traceSegment_075_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3358 8 9, g32p_row03_traceSegment_075_3358_0008, g32p_row03_traceSegment_075_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3341 17 17, g32p_row03_traceSegment_075_3341_0017, g32p_row03_traceSegment_075_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3307 34 34, g32p_row03_traceSegment_075_3307_0034, g32p_row03_traceSegment_075_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3240 67 68, g32p_row03_traceSegment_075_3240_0067, g32p_row03_traceSegment_075_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3391 8 9, g32p_row03_traceSegment_075_3391_0008, g32p_row03_traceSegment_075_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3375 16 17, g32p_row03_traceSegment_075_3375_0016, g32p_row03_traceSegment_075_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3408 8 9, g32p_row03_traceSegment_075_3408_0008, g32p_row03_traceSegment_075_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3425 8 9, g32p_row03_traceSegment_075_3425_0008, g32p_row03_traceSegment_075_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3408 17 17, g32p_row03_traceSegment_075_3408_0017, g32p_row03_traceSegment_075_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3375 33 34, g32p_row03_traceSegment_075_3375_0033, g32p_row03_traceSegment_075_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3442 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3442 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3442 8 9, g32p_row03_traceSegment_075_3442_0008, g32p_row03_traceSegment_075_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3459 8 9, g32p_row03_traceSegment_075_3459_0008, g32p_row03_traceSegment_075_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3442 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3442 17 17, g32p_row03_traceSegment_075_3442_0017, g32p_row03_traceSegment_075_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3476 8 9, g32p_row03_traceSegment_075_3476_0008, g32p_row03_traceSegment_075_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3493 8 9, g32p_row03_traceSegment_075_3493_0008, g32p_row03_traceSegment_075_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3476 17 17, g32p_row03_traceSegment_075_3476_0017, g32p_row03_traceSegment_075_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 3442 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3442 34 34, g32p_row03_traceSegment_075_3442_0034, g32p_row03_traceSegment_075_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 3375 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3375 67 68, g32p_row03_traceSegment_075_3375_0067, g32p_row03_traceSegment_075_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 3240 270 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3240 135 135, g32p_row03_traceSegment_075_3240_0135, g32p_row03_traceSegment_075_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3526 8 9, g32p_row03_traceSegment_075_3526_0008, g32p_row03_traceSegment_075_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3510 16 17, g32p_row03_traceSegment_075_3510_0016, g32p_row03_traceSegment_075_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3543 8 9, g32p_row03_traceSegment_075_3543_0008, g32p_row03_traceSegment_075_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3560 8 9, g32p_row03_traceSegment_075_3560_0008, g32p_row03_traceSegment_075_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3543 17 17, g32p_row03_traceSegment_075_3543_0017, g32p_row03_traceSegment_075_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3510 33 34, g32p_row03_traceSegment_075_3510_0033, g32p_row03_traceSegment_075_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3577 8 9, g32p_row03_traceSegment_075_3577_0008, g32p_row03_traceSegment_075_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3594 8 9, g32p_row03_traceSegment_075_3594_0008, g32p_row03_traceSegment_075_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3577 17 17, g32p_row03_traceSegment_075_3577_0017, g32p_row03_traceSegment_075_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3611 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3611 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3611 8 9, g32p_row03_traceSegment_075_3611_0008, g32p_row03_traceSegment_075_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3628 8 9, g32p_row03_traceSegment_075_3628_0008, g32p_row03_traceSegment_075_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3611 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3611 17 17, g32p_row03_traceSegment_075_3611_0017, g32p_row03_traceSegment_075_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 3577 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3577 34 34, g32p_row03_traceSegment_075_3577_0034, g32p_row03_traceSegment_075_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 3510 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3510 67 68, g32p_row03_traceSegment_075_3510_0067, g32p_row03_traceSegment_075_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3661 8 9, g32p_row03_traceSegment_075_3661_0008, g32p_row03_traceSegment_075_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3645 16 17, g32p_row03_traceSegment_075_3645_0016, g32p_row03_traceSegment_075_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3678 8 9, g32p_row03_traceSegment_075_3678_0008, g32p_row03_traceSegment_075_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3703 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3695 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3695 8 9, g32p_row03_traceSegment_075_3695_0008, g32p_row03_traceSegment_075_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3678 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3678 17 17, g32p_row03_traceSegment_075_3678_0017, g32p_row03_traceSegment_075_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 3645 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3645 33 34, g32p_row03_traceSegment_075_3645_0033, g32p_row03_traceSegment_075_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3712 8 9, g32p_row03_traceSegment_075_3712_0008, g32p_row03_traceSegment_075_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3737 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3729 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3729 8 9, g32p_row03_traceSegment_075_3729_0008, g32p_row03_traceSegment_075_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3712 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3712 17 17, g32p_row03_traceSegment_075_3712_0017, g32p_row03_traceSegment_075_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3746 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3746 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3746 8 9, g32p_row03_traceSegment_075_3746_0008, g32p_row03_traceSegment_075_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3763 8 9, g32p_row03_traceSegment_075_3763_0008, g32p_row03_traceSegment_075_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3746 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3746 17 17, g32p_row03_traceSegment_075_3746_0017, g32p_row03_traceSegment_075_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 3712 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3712 34 34, g32p_row03_traceSegment_075_3712_0034, g32p_row03_traceSegment_075_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 3645 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3645 67 68, g32p_row03_traceSegment_075_3645_0067, g32p_row03_traceSegment_075_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 3510 270 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3510 135 135, g32p_row03_traceSegment_075_3510_0135, g32p_row03_traceSegment_075_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_075 3240 540 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3240 270 270, g32p_row03_traceSegment_075_3240_0270, g32p_row03_traceSegment_075_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3796 8 9, g32p_row03_traceSegment_075_3796_0008, g32p_row03_traceSegment_075_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3780 16 17, g32p_row03_traceSegment_075_3780_0016, g32p_row03_traceSegment_075_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3821 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3813 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3813 8 9, g32p_row03_traceSegment_075_3813_0008, g32p_row03_traceSegment_075_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3830 8 9, g32p_row03_traceSegment_075_3830_0008, g32p_row03_traceSegment_075_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3813 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3813 17 17, g32p_row03_traceSegment_075_3813_0017, g32p_row03_traceSegment_075_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 3780 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3780 33 34, g32p_row03_traceSegment_075_3780_0033, g32p_row03_traceSegment_075_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3847 8 9, g32p_row03_traceSegment_075_3847_0008, g32p_row03_traceSegment_075_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3864 8 9, g32p_row03_traceSegment_075_3864_0008, g32p_row03_traceSegment_075_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3847 17 17, g32p_row03_traceSegment_075_3847_0017, g32p_row03_traceSegment_075_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3881 8 9, g32p_row03_traceSegment_075_3881_0008, g32p_row03_traceSegment_075_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3898 8 9, g32p_row03_traceSegment_075_3898_0008, g32p_row03_traceSegment_075_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3881 17 17, g32p_row03_traceSegment_075_3881_0017, g32p_row03_traceSegment_075_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3847 34 34, g32p_row03_traceSegment_075_3847_0034, g32p_row03_traceSegment_075_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 3780 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3780 67 68, g32p_row03_traceSegment_075_3780_0067, g32p_row03_traceSegment_075_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 3915 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3931 8 9, g32p_row03_traceSegment_075_3931_0008, g32p_row03_traceSegment_075_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 3915 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3915 16 17, g32p_row03_traceSegment_075_3915_0016, g32p_row03_traceSegment_075_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3948 8 9, g32p_row03_traceSegment_075_3948_0008, g32p_row03_traceSegment_075_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3965 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3965 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3965 8 9, g32p_row03_traceSegment_075_3965_0008, g32p_row03_traceSegment_075_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3948 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3948 17 17, g32p_row03_traceSegment_075_3948_0017, g32p_row03_traceSegment_075_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 3915 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3915 33 34, g32p_row03_traceSegment_075_3915_0033, g32p_row03_traceSegment_075_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3982 8 9, g32p_row03_traceSegment_075_3982_0008, g32p_row03_traceSegment_075_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3999 8 9, g32p_row03_traceSegment_075_3999_0008, g32p_row03_traceSegment_075_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3982 17 17, g32p_row03_traceSegment_075_3982_0017, g32p_row03_traceSegment_075_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4016 8 9, g32p_row03_traceSegment_075_4016_0008, g32p_row03_traceSegment_075_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4041 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4033 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4033 8 9, g32p_row03_traceSegment_075_4033_0008, g32p_row03_traceSegment_075_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 4016 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4016 17 17, g32p_row03_traceSegment_075_4016_0017, g32p_row03_traceSegment_075_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 3982 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3982 34 34, g32p_row03_traceSegment_075_3982_0034, g32p_row03_traceSegment_075_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 3915 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3915 67 68, g32p_row03_traceSegment_075_3915_0067, g32p_row03_traceSegment_075_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 3780 270 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3780 135 135, g32p_row03_traceSegment_075_3780_0135, g32p_row03_traceSegment_075_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4066 8 9, g32p_row03_traceSegment_075_4066_0008, g32p_row03_traceSegment_075_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4050 16 17, g32p_row03_traceSegment_075_4050_0016, g32p_row03_traceSegment_075_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4083 8 9, g32p_row03_traceSegment_075_4083_0008, g32p_row03_traceSegment_075_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4100 8 9, g32p_row03_traceSegment_075_4100_0008, g32p_row03_traceSegment_075_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4083 17 17, g32p_row03_traceSegment_075_4083_0017, g32p_row03_traceSegment_075_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4050 33 34, g32p_row03_traceSegment_075_4050_0033, g32p_row03_traceSegment_075_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4117 8 9, g32p_row03_traceSegment_075_4117_0008, g32p_row03_traceSegment_075_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4134 8 9, g32p_row03_traceSegment_075_4134_0008, g32p_row03_traceSegment_075_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4117 17 17, g32p_row03_traceSegment_075_4117_0017, g32p_row03_traceSegment_075_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4151 8 9, g32p_row03_traceSegment_075_4151_0008, g32p_row03_traceSegment_075_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4168 8 9, g32p_row03_traceSegment_075_4168_0008, g32p_row03_traceSegment_075_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4151 17 17, g32p_row03_traceSegment_075_4151_0017, g32p_row03_traceSegment_075_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4117 34 34, g32p_row03_traceSegment_075_4117_0034, g32p_row03_traceSegment_075_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4050 67 68, g32p_row03_traceSegment_075_4050_0067, g32p_row03_traceSegment_075_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_075 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4201 8 9, g32p_row03_traceSegment_075_4201_0008, g32p_row03_traceSegment_075_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_075 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4185 16 17, g32p_row03_traceSegment_075_4185_0016, g32p_row03_traceSegment_075_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4218 8 9, g32p_row03_traceSegment_075_4218_0008, g32p_row03_traceSegment_075_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4243 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4235 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4235 8 9, g32p_row03_traceSegment_075_4235_0008, g32p_row03_traceSegment_075_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 4218 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4218 17 17, g32p_row03_traceSegment_075_4218_0017, g32p_row03_traceSegment_075_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_075 4185 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4185 33 34, g32p_row03_traceSegment_075_4185_0033, g32p_row03_traceSegment_075_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4252 8 9, g32p_row03_traceSegment_075_4252_0008, g32p_row03_traceSegment_075_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4277 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4269 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4269 8 9, g32p_row03_traceSegment_075_4269_0008, g32p_row03_traceSegment_075_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 4252 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4252 17 17, g32p_row03_traceSegment_075_4252_0017, g32p_row03_traceSegment_075_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4286 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4286 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4286 8 9, g32p_row03_traceSegment_075_4286_0008, g32p_row03_traceSegment_075_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_075 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_075 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_075_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_075 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4303 8 9, g32p_row03_traceSegment_075_4303_0008, g32p_row03_traceSegment_075_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_075 4286 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4286 17 17, g32p_row03_traceSegment_075_4286_0017, g32p_row03_traceSegment_075_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_075 4252 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4252 34 34, g32p_row03_traceSegment_075_4252_0034, g32p_row03_traceSegment_075_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_075 4185 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4185 67 68, g32p_row03_traceSegment_075_4185_0067, g32p_row03_traceSegment_075_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_075_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_075 4050 270 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 4050 135 135, g32p_row03_traceSegment_075_4050_0135, g32p_row03_traceSegment_075_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_075 3780 540 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3780 270 270, g32p_row03_traceSegment_075_3780_0270, g32p_row03_traceSegment_075_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_075_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_075 3240 1080 = [12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 3240 540 540, g32p_row03_traceSegment_075_3240_0540, g32p_row03_traceSegment_075_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_075_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_075 2160 2160 = [34] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 2160 1080 1080, g32p_row03_traceSegment_075_2160_1080, g32p_row03_traceSegment_075_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_075_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_075 0 4320 = [40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_075 0 2160 2160, g32p_row03_traceSegment_075_0000_2160, g32p_row03_traceSegment_075_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 75 = [40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_075_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_078 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 78 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_078_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 16 8 9, g32p_row03_traceSegment_078_0016_0008, g32p_row03_traceSegment_078_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 0 16 17, g32p_row03_traceSegment_078_0000_0016, g32p_row03_traceSegment_078_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 33 8 9, g32p_row03_traceSegment_078_0033_0008, g32p_row03_traceSegment_078_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 50 8 9, g32p_row03_traceSegment_078_0050_0008, g32p_row03_traceSegment_078_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 33 17 17, g32p_row03_traceSegment_078_0033_0017, g32p_row03_traceSegment_078_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 0 33 34, g32p_row03_traceSegment_078_0000_0033, g32p_row03_traceSegment_078_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 67 8 9, g32p_row03_traceSegment_078_0067_0008, g32p_row03_traceSegment_078_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 84 8 9, g32p_row03_traceSegment_078_0084_0008, g32p_row03_traceSegment_078_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 67 17 17, g32p_row03_traceSegment_078_0067_0017, g32p_row03_traceSegment_078_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 101 8 9, g32p_row03_traceSegment_078_0101_0008, g32p_row03_traceSegment_078_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 118 8 9, g32p_row03_traceSegment_078_0118_0008, g32p_row03_traceSegment_078_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 101 17 17, g32p_row03_traceSegment_078_0101_0017, g32p_row03_traceSegment_078_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 67 34 34, g32p_row03_traceSegment_078_0067_0034, g32p_row03_traceSegment_078_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 0 67 68, g32p_row03_traceSegment_078_0000_0067, g32p_row03_traceSegment_078_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 151 8 9, g32p_row03_traceSegment_078_0151_0008, g32p_row03_traceSegment_078_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 135 16 17, g32p_row03_traceSegment_078_0135_0016, g32p_row03_traceSegment_078_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 168 8 9, g32p_row03_traceSegment_078_0168_0008, g32p_row03_traceSegment_078_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 185 8 9, g32p_row03_traceSegment_078_0185_0008, g32p_row03_traceSegment_078_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 168 17 17, g32p_row03_traceSegment_078_0168_0017, g32p_row03_traceSegment_078_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 135 33 34, g32p_row03_traceSegment_078_0135_0033, g32p_row03_traceSegment_078_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 202 8 9, g32p_row03_traceSegment_078_0202_0008, g32p_row03_traceSegment_078_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 219 8 9, g32p_row03_traceSegment_078_0219_0008, g32p_row03_traceSegment_078_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 202 17 17, g32p_row03_traceSegment_078_0202_0017, g32p_row03_traceSegment_078_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 236 8 9, g32p_row03_traceSegment_078_0236_0008, g32p_row03_traceSegment_078_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 253 8 9, g32p_row03_traceSegment_078_0253_0008, g32p_row03_traceSegment_078_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 236 17 17, g32p_row03_traceSegment_078_0236_0017, g32p_row03_traceSegment_078_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 202 34 34, g32p_row03_traceSegment_078_0202_0034, g32p_row03_traceSegment_078_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 135 67 68, g32p_row03_traceSegment_078_0135_0067, g32p_row03_traceSegment_078_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 0 135 135, g32p_row03_traceSegment_078_0000_0135, g32p_row03_traceSegment_078_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 270 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 286 8 9, g32p_row03_traceSegment_078_0286_0008, g32p_row03_traceSegment_078_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 270 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 270 16 17, g32p_row03_traceSegment_078_0270_0016, g32p_row03_traceSegment_078_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 303 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 303 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 303 8 9, g32p_row03_traceSegment_078_0303_0008, g32p_row03_traceSegment_078_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 320 8 9, g32p_row03_traceSegment_078_0320_0008, g32p_row03_traceSegment_078_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 303 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 303 17 17, g32p_row03_traceSegment_078_0303_0017, g32p_row03_traceSegment_078_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 270 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 270 33 34, g32p_row03_traceSegment_078_0270_0033, g32p_row03_traceSegment_078_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 337 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 337 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 337 8 9, g32p_row03_traceSegment_078_0337_0008, g32p_row03_traceSegment_078_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 354 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 354 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 354 8 9, g32p_row03_traceSegment_078_0354_0008, g32p_row03_traceSegment_078_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 337 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 337 17 17, g32p_row03_traceSegment_078_0337_0017, g32p_row03_traceSegment_078_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 371 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 379 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 371 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 371 8 9, g32p_row03_traceSegment_078_0371_0008, g32p_row03_traceSegment_078_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 388 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 396 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 388 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 388 8 9, g32p_row03_traceSegment_078_0388_0008, g32p_row03_traceSegment_078_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 371 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 371 17 17, g32p_row03_traceSegment_078_0371_0017, g32p_row03_traceSegment_078_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 337 68 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 337 34 34, g32p_row03_traceSegment_078_0337_0034, g32p_row03_traceSegment_078_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 270 135 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 270 67 68, g32p_row03_traceSegment_078_0270_0067, g32p_row03_traceSegment_078_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 421 8 9, g32p_row03_traceSegment_078_0421_0008, g32p_row03_traceSegment_078_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 405 16 17, g32p_row03_traceSegment_078_0405_0016, g32p_row03_traceSegment_078_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 438 8 9, g32p_row03_traceSegment_078_0438_0008, g32p_row03_traceSegment_078_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 455 8 9, g32p_row03_traceSegment_078_0455_0008, g32p_row03_traceSegment_078_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 438 17 17, g32p_row03_traceSegment_078_0438_0017, g32p_row03_traceSegment_078_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 405 33 34, g32p_row03_traceSegment_078_0405_0033, g32p_row03_traceSegment_078_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 472 8 9, g32p_row03_traceSegment_078_0472_0008, g32p_row03_traceSegment_078_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 489 8 9, g32p_row03_traceSegment_078_0489_0008, g32p_row03_traceSegment_078_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 472 17 17, g32p_row03_traceSegment_078_0472_0017, g32p_row03_traceSegment_078_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 506 8 9, g32p_row03_traceSegment_078_0506_0008, g32p_row03_traceSegment_078_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 523 8 9, g32p_row03_traceSegment_078_0523_0008, g32p_row03_traceSegment_078_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 506 17 17, g32p_row03_traceSegment_078_0506_0017, g32p_row03_traceSegment_078_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 472 34 34, g32p_row03_traceSegment_078_0472_0034, g32p_row03_traceSegment_078_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 405 67 68, g32p_row03_traceSegment_078_0405_0067, g32p_row03_traceSegment_078_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 270 270 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 270 135 135, g32p_row03_traceSegment_078_0270_0135, g32p_row03_traceSegment_078_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_078 0 540 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 0 270 270, g32p_row03_traceSegment_078_0000_0270, g32p_row03_traceSegment_078_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 556 8 9, g32p_row03_traceSegment_078_0556_0008, g32p_row03_traceSegment_078_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 540 16 17, g32p_row03_traceSegment_078_0540_0016, g32p_row03_traceSegment_078_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 573 8 9, g32p_row03_traceSegment_078_0573_0008, g32p_row03_traceSegment_078_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 590 8 9, g32p_row03_traceSegment_078_0590_0008, g32p_row03_traceSegment_078_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 573 17 17, g32p_row03_traceSegment_078_0573_0017, g32p_row03_traceSegment_078_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 540 33 34, g32p_row03_traceSegment_078_0540_0033, g32p_row03_traceSegment_078_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 607 8 9, g32p_row03_traceSegment_078_0607_0008, g32p_row03_traceSegment_078_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 624 8 9, g32p_row03_traceSegment_078_0624_0008, g32p_row03_traceSegment_078_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 607 17 17, g32p_row03_traceSegment_078_0607_0017, g32p_row03_traceSegment_078_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 641 8 9, g32p_row03_traceSegment_078_0641_0008, g32p_row03_traceSegment_078_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 658 8 9, g32p_row03_traceSegment_078_0658_0008, g32p_row03_traceSegment_078_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 641 17 17, g32p_row03_traceSegment_078_0641_0017, g32p_row03_traceSegment_078_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 607 34 34, g32p_row03_traceSegment_078_0607_0034, g32p_row03_traceSegment_078_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 540 67 68, g32p_row03_traceSegment_078_0540_0067, g32p_row03_traceSegment_078_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 691 8 9, g32p_row03_traceSegment_078_0691_0008, g32p_row03_traceSegment_078_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 675 16 17, g32p_row03_traceSegment_078_0675_0016, g32p_row03_traceSegment_078_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 708 8 9, g32p_row03_traceSegment_078_0708_0008, g32p_row03_traceSegment_078_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 725 8 9, g32p_row03_traceSegment_078_0725_0008, g32p_row03_traceSegment_078_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 708 17 17, g32p_row03_traceSegment_078_0708_0017, g32p_row03_traceSegment_078_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 675 33 34, g32p_row03_traceSegment_078_0675_0033, g32p_row03_traceSegment_078_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 742 8 9, g32p_row03_traceSegment_078_0742_0008, g32p_row03_traceSegment_078_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 759 8 9, g32p_row03_traceSegment_078_0759_0008, g32p_row03_traceSegment_078_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 742 17 17, g32p_row03_traceSegment_078_0742_0017, g32p_row03_traceSegment_078_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 776 8 9, g32p_row03_traceSegment_078_0776_0008, g32p_row03_traceSegment_078_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 793 8 9, g32p_row03_traceSegment_078_0793_0008, g32p_row03_traceSegment_078_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 776 17 17, g32p_row03_traceSegment_078_0776_0017, g32p_row03_traceSegment_078_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 742 34 34, g32p_row03_traceSegment_078_0742_0034, g32p_row03_traceSegment_078_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 675 67 68, g32p_row03_traceSegment_078_0675_0067, g32p_row03_traceSegment_078_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 540 135 135, g32p_row03_traceSegment_078_0540_0135, g32p_row03_traceSegment_078_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 826 8 9, g32p_row03_traceSegment_078_0826_0008, g32p_row03_traceSegment_078_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 810 16 17, g32p_row03_traceSegment_078_0810_0016, g32p_row03_traceSegment_078_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 843 8 9, g32p_row03_traceSegment_078_0843_0008, g32p_row03_traceSegment_078_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 860 8 9, g32p_row03_traceSegment_078_0860_0008, g32p_row03_traceSegment_078_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 843 17 17, g32p_row03_traceSegment_078_0843_0017, g32p_row03_traceSegment_078_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 810 33 34, g32p_row03_traceSegment_078_0810_0033, g32p_row03_traceSegment_078_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 877 8 9, g32p_row03_traceSegment_078_0877_0008, g32p_row03_traceSegment_078_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 894 8 9, g32p_row03_traceSegment_078_0894_0008, g32p_row03_traceSegment_078_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 877 17 17, g32p_row03_traceSegment_078_0877_0017, g32p_row03_traceSegment_078_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 911 8 9, g32p_row03_traceSegment_078_0911_0008, g32p_row03_traceSegment_078_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 928 8 9, g32p_row03_traceSegment_078_0928_0008, g32p_row03_traceSegment_078_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 911 17 17, g32p_row03_traceSegment_078_0911_0017, g32p_row03_traceSegment_078_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 877 34 34, g32p_row03_traceSegment_078_0877_0034, g32p_row03_traceSegment_078_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 810 67 68, g32p_row03_traceSegment_078_0810_0067, g32p_row03_traceSegment_078_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 961 8 9, g32p_row03_traceSegment_078_0961_0008, g32p_row03_traceSegment_078_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 945 16 17, g32p_row03_traceSegment_078_0945_0016, g32p_row03_traceSegment_078_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 978 8 9, g32p_row03_traceSegment_078_0978_0008, g32p_row03_traceSegment_078_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 995 8 9, g32p_row03_traceSegment_078_0995_0008, g32p_row03_traceSegment_078_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 978 17 17, g32p_row03_traceSegment_078_0978_0017, g32p_row03_traceSegment_078_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 945 33 34, g32p_row03_traceSegment_078_0945_0033, g32p_row03_traceSegment_078_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1012 8 9, g32p_row03_traceSegment_078_1012_0008, g32p_row03_traceSegment_078_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1029 8 9, g32p_row03_traceSegment_078_1029_0008, g32p_row03_traceSegment_078_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1012 17 17, g32p_row03_traceSegment_078_1012_0017, g32p_row03_traceSegment_078_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1046 8 9, g32p_row03_traceSegment_078_1046_0008, g32p_row03_traceSegment_078_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1063 8 9, g32p_row03_traceSegment_078_1063_0008, g32p_row03_traceSegment_078_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1046 17 17, g32p_row03_traceSegment_078_1046_0017, g32p_row03_traceSegment_078_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1012 34 34, g32p_row03_traceSegment_078_1012_0034, g32p_row03_traceSegment_078_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 945 67 68, g32p_row03_traceSegment_078_0945_0067, g32p_row03_traceSegment_078_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 810 135 135, g32p_row03_traceSegment_078_0810_0135, g32p_row03_traceSegment_078_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_078 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 540 270 270, g32p_row03_traceSegment_078_0540_0270, g32p_row03_traceSegment_078_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_078 0 1080 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 0 540 540, g32p_row03_traceSegment_078_0000_0540, g32p_row03_traceSegment_078_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1096 8 9, g32p_row03_traceSegment_078_1096_0008, g32p_row03_traceSegment_078_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1080 16 17, g32p_row03_traceSegment_078_1080_0016, g32p_row03_traceSegment_078_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1113 8 9, g32p_row03_traceSegment_078_1113_0008, g32p_row03_traceSegment_078_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1130 8 9, g32p_row03_traceSegment_078_1130_0008, g32p_row03_traceSegment_078_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1113 17 17, g32p_row03_traceSegment_078_1113_0017, g32p_row03_traceSegment_078_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1080 33 34, g32p_row03_traceSegment_078_1080_0033, g32p_row03_traceSegment_078_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1147 8 9, g32p_row03_traceSegment_078_1147_0008, g32p_row03_traceSegment_078_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1164 8 9, g32p_row03_traceSegment_078_1164_0008, g32p_row03_traceSegment_078_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1147 17 17, g32p_row03_traceSegment_078_1147_0017, g32p_row03_traceSegment_078_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1181 8 9, g32p_row03_traceSegment_078_1181_0008, g32p_row03_traceSegment_078_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1198 8 9, g32p_row03_traceSegment_078_1198_0008, g32p_row03_traceSegment_078_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1181 17 17, g32p_row03_traceSegment_078_1181_0017, g32p_row03_traceSegment_078_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1147 34 34, g32p_row03_traceSegment_078_1147_0034, g32p_row03_traceSegment_078_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1080 67 68, g32p_row03_traceSegment_078_1080_0067, g32p_row03_traceSegment_078_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1231 8 9, g32p_row03_traceSegment_078_1231_0008, g32p_row03_traceSegment_078_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1215 16 17, g32p_row03_traceSegment_078_1215_0016, g32p_row03_traceSegment_078_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1248 8 9, g32p_row03_traceSegment_078_1248_0008, g32p_row03_traceSegment_078_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1265 8 9, g32p_row03_traceSegment_078_1265_0008, g32p_row03_traceSegment_078_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1248 17 17, g32p_row03_traceSegment_078_1248_0017, g32p_row03_traceSegment_078_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1215 33 34, g32p_row03_traceSegment_078_1215_0033, g32p_row03_traceSegment_078_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1282 8 9, g32p_row03_traceSegment_078_1282_0008, g32p_row03_traceSegment_078_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1299 8 9, g32p_row03_traceSegment_078_1299_0008, g32p_row03_traceSegment_078_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1282 17 17, g32p_row03_traceSegment_078_1282_0017, g32p_row03_traceSegment_078_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1316 8 9, g32p_row03_traceSegment_078_1316_0008, g32p_row03_traceSegment_078_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1333 8 9, g32p_row03_traceSegment_078_1333_0008, g32p_row03_traceSegment_078_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1316 17 17, g32p_row03_traceSegment_078_1316_0017, g32p_row03_traceSegment_078_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1282 34 34, g32p_row03_traceSegment_078_1282_0034, g32p_row03_traceSegment_078_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1215 67 68, g32p_row03_traceSegment_078_1215_0067, g32p_row03_traceSegment_078_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1080 135 135, g32p_row03_traceSegment_078_1080_0135, g32p_row03_traceSegment_078_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1366 8 9, g32p_row03_traceSegment_078_1366_0008, g32p_row03_traceSegment_078_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1350 16 17, g32p_row03_traceSegment_078_1350_0016, g32p_row03_traceSegment_078_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1383 8 9, g32p_row03_traceSegment_078_1383_0008, g32p_row03_traceSegment_078_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1400 8 9, g32p_row03_traceSegment_078_1400_0008, g32p_row03_traceSegment_078_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1383 17 17, g32p_row03_traceSegment_078_1383_0017, g32p_row03_traceSegment_078_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1350 33 34, g32p_row03_traceSegment_078_1350_0033, g32p_row03_traceSegment_078_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1417 8 9, g32p_row03_traceSegment_078_1417_0008, g32p_row03_traceSegment_078_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1434 8 9, g32p_row03_traceSegment_078_1434_0008, g32p_row03_traceSegment_078_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1417 17 17, g32p_row03_traceSegment_078_1417_0017, g32p_row03_traceSegment_078_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1451 8 9, g32p_row03_traceSegment_078_1451_0008, g32p_row03_traceSegment_078_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1468 8 9, g32p_row03_traceSegment_078_1468_0008, g32p_row03_traceSegment_078_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1451 17 17, g32p_row03_traceSegment_078_1451_0017, g32p_row03_traceSegment_078_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1417 34 34, g32p_row03_traceSegment_078_1417_0034, g32p_row03_traceSegment_078_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1350 67 68, g32p_row03_traceSegment_078_1350_0067, g32p_row03_traceSegment_078_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1501 8 9, g32p_row03_traceSegment_078_1501_0008, g32p_row03_traceSegment_078_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1485 16 17, g32p_row03_traceSegment_078_1485_0016, g32p_row03_traceSegment_078_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1518 8 9, g32p_row03_traceSegment_078_1518_0008, g32p_row03_traceSegment_078_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1535 8 9, g32p_row03_traceSegment_078_1535_0008, g32p_row03_traceSegment_078_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1518 17 17, g32p_row03_traceSegment_078_1518_0017, g32p_row03_traceSegment_078_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1485 33 34, g32p_row03_traceSegment_078_1485_0033, g32p_row03_traceSegment_078_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1552 8 9, g32p_row03_traceSegment_078_1552_0008, g32p_row03_traceSegment_078_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1569 8 9, g32p_row03_traceSegment_078_1569_0008, g32p_row03_traceSegment_078_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1552 17 17, g32p_row03_traceSegment_078_1552_0017, g32p_row03_traceSegment_078_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1586 8 9, g32p_row03_traceSegment_078_1586_0008, g32p_row03_traceSegment_078_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1603 8 9, g32p_row03_traceSegment_078_1603_0008, g32p_row03_traceSegment_078_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1586 17 17, g32p_row03_traceSegment_078_1586_0017, g32p_row03_traceSegment_078_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1552 34 34, g32p_row03_traceSegment_078_1552_0034, g32p_row03_traceSegment_078_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1485 67 68, g32p_row03_traceSegment_078_1485_0067, g32p_row03_traceSegment_078_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1350 135 135, g32p_row03_traceSegment_078_1350_0135, g32p_row03_traceSegment_078_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_078 1080 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1080 270 270, g32p_row03_traceSegment_078_1080_0270, g32p_row03_traceSegment_078_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1636 8 9, g32p_row03_traceSegment_078_1636_0008, g32p_row03_traceSegment_078_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1620 16 17, g32p_row03_traceSegment_078_1620_0016, g32p_row03_traceSegment_078_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1653 8 9, g32p_row03_traceSegment_078_1653_0008, g32p_row03_traceSegment_078_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1670 8 9, g32p_row03_traceSegment_078_1670_0008, g32p_row03_traceSegment_078_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1653 17 17, g32p_row03_traceSegment_078_1653_0017, g32p_row03_traceSegment_078_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1620 33 34, g32p_row03_traceSegment_078_1620_0033, g32p_row03_traceSegment_078_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1687 8 9, g32p_row03_traceSegment_078_1687_0008, g32p_row03_traceSegment_078_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1704 8 9, g32p_row03_traceSegment_078_1704_0008, g32p_row03_traceSegment_078_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1687 17 17, g32p_row03_traceSegment_078_1687_0017, g32p_row03_traceSegment_078_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1721 8 9, g32p_row03_traceSegment_078_1721_0008, g32p_row03_traceSegment_078_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1738 8 9, g32p_row03_traceSegment_078_1738_0008, g32p_row03_traceSegment_078_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1721 17 17, g32p_row03_traceSegment_078_1721_0017, g32p_row03_traceSegment_078_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1687 34 34, g32p_row03_traceSegment_078_1687_0034, g32p_row03_traceSegment_078_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1620 67 68, g32p_row03_traceSegment_078_1620_0067, g32p_row03_traceSegment_078_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1771 8 9, g32p_row03_traceSegment_078_1771_0008, g32p_row03_traceSegment_078_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1755 16 17, g32p_row03_traceSegment_078_1755_0016, g32p_row03_traceSegment_078_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1788 8 9, g32p_row03_traceSegment_078_1788_0008, g32p_row03_traceSegment_078_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1805 8 9, g32p_row03_traceSegment_078_1805_0008, g32p_row03_traceSegment_078_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1788 17 17, g32p_row03_traceSegment_078_1788_0017, g32p_row03_traceSegment_078_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1755 33 34, g32p_row03_traceSegment_078_1755_0033, g32p_row03_traceSegment_078_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1822 8 9, g32p_row03_traceSegment_078_1822_0008, g32p_row03_traceSegment_078_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1839 8 9, g32p_row03_traceSegment_078_1839_0008, g32p_row03_traceSegment_078_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1822 17 17, g32p_row03_traceSegment_078_1822_0017, g32p_row03_traceSegment_078_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1856 8 9, g32p_row03_traceSegment_078_1856_0008, g32p_row03_traceSegment_078_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1873 8 9, g32p_row03_traceSegment_078_1873_0008, g32p_row03_traceSegment_078_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1856 17 17, g32p_row03_traceSegment_078_1856_0017, g32p_row03_traceSegment_078_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1822 34 34, g32p_row03_traceSegment_078_1822_0034, g32p_row03_traceSegment_078_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1755 67 68, g32p_row03_traceSegment_078_1755_0067, g32p_row03_traceSegment_078_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1620 135 135, g32p_row03_traceSegment_078_1620_0135, g32p_row03_traceSegment_078_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1906 8 9, g32p_row03_traceSegment_078_1906_0008, g32p_row03_traceSegment_078_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1890 16 17, g32p_row03_traceSegment_078_1890_0016, g32p_row03_traceSegment_078_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1923 8 9, g32p_row03_traceSegment_078_1923_0008, g32p_row03_traceSegment_078_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1940 8 9, g32p_row03_traceSegment_078_1940_0008, g32p_row03_traceSegment_078_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1923 17 17, g32p_row03_traceSegment_078_1923_0017, g32p_row03_traceSegment_078_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1890 33 34, g32p_row03_traceSegment_078_1890_0033, g32p_row03_traceSegment_078_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1957 8 9, g32p_row03_traceSegment_078_1957_0008, g32p_row03_traceSegment_078_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1974 8 9, g32p_row03_traceSegment_078_1974_0008, g32p_row03_traceSegment_078_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1957 17 17, g32p_row03_traceSegment_078_1957_0017, g32p_row03_traceSegment_078_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1991 8 9, g32p_row03_traceSegment_078_1991_0008, g32p_row03_traceSegment_078_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2008 8 9, g32p_row03_traceSegment_078_2008_0008, g32p_row03_traceSegment_078_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1991 17 17, g32p_row03_traceSegment_078_1991_0017, g32p_row03_traceSegment_078_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1957 34 34, g32p_row03_traceSegment_078_1957_0034, g32p_row03_traceSegment_078_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1890 67 68, g32p_row03_traceSegment_078_1890_0067, g32p_row03_traceSegment_078_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2041 8 9, g32p_row03_traceSegment_078_2041_0008, g32p_row03_traceSegment_078_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2025 16 17, g32p_row03_traceSegment_078_2025_0016, g32p_row03_traceSegment_078_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2058 8 9, g32p_row03_traceSegment_078_2058_0008, g32p_row03_traceSegment_078_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2075 8 9, g32p_row03_traceSegment_078_2075_0008, g32p_row03_traceSegment_078_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2058 17 17, g32p_row03_traceSegment_078_2058_0017, g32p_row03_traceSegment_078_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2025 33 34, g32p_row03_traceSegment_078_2025_0033, g32p_row03_traceSegment_078_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2092 8 9, g32p_row03_traceSegment_078_2092_0008, g32p_row03_traceSegment_078_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2109 8 9, g32p_row03_traceSegment_078_2109_0008, g32p_row03_traceSegment_078_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2092 17 17, g32p_row03_traceSegment_078_2092_0017, g32p_row03_traceSegment_078_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2126 8 9, g32p_row03_traceSegment_078_2126_0008, g32p_row03_traceSegment_078_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2143 8 9, g32p_row03_traceSegment_078_2143_0008, g32p_row03_traceSegment_078_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2126 17 17, g32p_row03_traceSegment_078_2126_0017, g32p_row03_traceSegment_078_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2092 34 34, g32p_row03_traceSegment_078_2092_0034, g32p_row03_traceSegment_078_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2025 67 68, g32p_row03_traceSegment_078_2025_0067, g32p_row03_traceSegment_078_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 1890 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1890 135 135, g32p_row03_traceSegment_078_1890_0135, g32p_row03_traceSegment_078_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_078 1620 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1620 270 270, g32p_row03_traceSegment_078_1620_0270, g32p_row03_traceSegment_078_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_078_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_078 1080 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 1080 540 540, g32p_row03_traceSegment_078_1080_0540, g32p_row03_traceSegment_078_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_078 0 2160 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 0 1080 1080, g32p_row03_traceSegment_078_0000_1080, g32p_row03_traceSegment_078_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2176 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2176 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2176 8 9, g32p_row03_traceSegment_078_2176_0008, g32p_row03_traceSegment_078_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 2160 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2160 16 17, g32p_row03_traceSegment_078_2160_0016, g32p_row03_traceSegment_078_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2193 8 9, g32p_row03_traceSegment_078_2193_0008, g32p_row03_traceSegment_078_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2210 8 9, g32p_row03_traceSegment_078_2210_0008, g32p_row03_traceSegment_078_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2193 17 17, g32p_row03_traceSegment_078_2193_0017, g32p_row03_traceSegment_078_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 2160 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2160 33 34, g32p_row03_traceSegment_078_2160_0033, g32p_row03_traceSegment_078_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2227 8 9, g32p_row03_traceSegment_078_2227_0008, g32p_row03_traceSegment_078_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2244 8 9, g32p_row03_traceSegment_078_2244_0008, g32p_row03_traceSegment_078_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2227 17 17, g32p_row03_traceSegment_078_2227_0017, g32p_row03_traceSegment_078_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2261 8 9, g32p_row03_traceSegment_078_2261_0008, g32p_row03_traceSegment_078_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2278 8 9, g32p_row03_traceSegment_078_2278_0008, g32p_row03_traceSegment_078_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2261 17 17, g32p_row03_traceSegment_078_2261_0017, g32p_row03_traceSegment_078_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2227 34 34, g32p_row03_traceSegment_078_2227_0034, g32p_row03_traceSegment_078_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 2160 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2160 67 68, g32p_row03_traceSegment_078_2160_0067, g32p_row03_traceSegment_078_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2311 8 9, g32p_row03_traceSegment_078_2311_0008, g32p_row03_traceSegment_078_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2295 16 17, g32p_row03_traceSegment_078_2295_0016, g32p_row03_traceSegment_078_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2328 8 9, g32p_row03_traceSegment_078_2328_0008, g32p_row03_traceSegment_078_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2345 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2345 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2345 8 9, g32p_row03_traceSegment_078_2345_0008, g32p_row03_traceSegment_078_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2328 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2328 17 17, g32p_row03_traceSegment_078_2328_0017, g32p_row03_traceSegment_078_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 2295 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2295 33 34, g32p_row03_traceSegment_078_2295_0033, g32p_row03_traceSegment_078_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2370 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2362 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2362 8 9, g32p_row03_traceSegment_078_2362_0008, g32p_row03_traceSegment_078_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2379 8 9, g32p_row03_traceSegment_078_2379_0008, g32p_row03_traceSegment_078_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2362 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2362 17 17, g32p_row03_traceSegment_078_2362_0017, g32p_row03_traceSegment_078_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2404 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2396 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2396 8 9, g32p_row03_traceSegment_078_2396_0008, g32p_row03_traceSegment_078_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2413 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2421 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2413 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2413 8 9, g32p_row03_traceSegment_078_2413_0008, g32p_row03_traceSegment_078_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2396 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2396 17 17, g32p_row03_traceSegment_078_2396_0017, g32p_row03_traceSegment_078_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 2362 68 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2362 34 34, g32p_row03_traceSegment_078_2362_0034, g32p_row03_traceSegment_078_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 2295 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2295 67 68, g32p_row03_traceSegment_078_2295_0067, g32p_row03_traceSegment_078_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 2160 270 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2160 135 135, g32p_row03_traceSegment_078_2160_0135, g32p_row03_traceSegment_078_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 2430 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2454 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2446 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2446 8 9, g32p_row03_traceSegment_078_2446_0008, g32p_row03_traceSegment_078_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 2430 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2430 16 17, g32p_row03_traceSegment_078_2430_0016, g32p_row03_traceSegment_078_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2463 8 9, g32p_row03_traceSegment_078_2463_0008, g32p_row03_traceSegment_078_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2480 8 9, g32p_row03_traceSegment_078_2480_0008, g32p_row03_traceSegment_078_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2463 17 17, g32p_row03_traceSegment_078_2463_0017, g32p_row03_traceSegment_078_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 2430 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2430 33 34, g32p_row03_traceSegment_078_2430_0033, g32p_row03_traceSegment_078_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2497 8 9, g32p_row03_traceSegment_078_2497_0008, g32p_row03_traceSegment_078_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2514 8 9, g32p_row03_traceSegment_078_2514_0008, g32p_row03_traceSegment_078_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2497 17 17, g32p_row03_traceSegment_078_2497_0017, g32p_row03_traceSegment_078_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2531 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2531 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2531 8 9, g32p_row03_traceSegment_078_2531_0008, g32p_row03_traceSegment_078_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2548 8 9, g32p_row03_traceSegment_078_2548_0008, g32p_row03_traceSegment_078_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2531 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2531 17 17, g32p_row03_traceSegment_078_2531_0017, g32p_row03_traceSegment_078_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 2497 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2497 34 34, g32p_row03_traceSegment_078_2497_0034, g32p_row03_traceSegment_078_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 2430 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2430 67 68, g32p_row03_traceSegment_078_2430_0067, g32p_row03_traceSegment_078_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2581 8 9, g32p_row03_traceSegment_078_2581_0008, g32p_row03_traceSegment_078_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2565 16 17, g32p_row03_traceSegment_078_2565_0016, g32p_row03_traceSegment_078_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2606 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2598 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2598 8 9, g32p_row03_traceSegment_078_2598_0008, g32p_row03_traceSegment_078_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2615 8 9, g32p_row03_traceSegment_078_2615_0008, g32p_row03_traceSegment_078_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2598 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2598 17 17, g32p_row03_traceSegment_078_2598_0017, g32p_row03_traceSegment_078_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 2565 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2565 33 34, g32p_row03_traceSegment_078_2565_0033, g32p_row03_traceSegment_078_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2632 8 9, g32p_row03_traceSegment_078_2632_0008, g32p_row03_traceSegment_078_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2649 8 9, g32p_row03_traceSegment_078_2649_0008, g32p_row03_traceSegment_078_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2632 17 17, g32p_row03_traceSegment_078_2632_0017, g32p_row03_traceSegment_078_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2674 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2666 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2666 8 9, g32p_row03_traceSegment_078_2666_0008, g32p_row03_traceSegment_078_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2691 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2683 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2683 8 9, g32p_row03_traceSegment_078_2683_0008, g32p_row03_traceSegment_078_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2666 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2666 17 17, g32p_row03_traceSegment_078_2666_0017, g32p_row03_traceSegment_078_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 2632 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2632 34 34, g32p_row03_traceSegment_078_2632_0034, g32p_row03_traceSegment_078_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 2565 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2565 67 68, g32p_row03_traceSegment_078_2565_0067, g32p_row03_traceSegment_078_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 2430 270 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2430 135 135, g32p_row03_traceSegment_078_2430_0135, g32p_row03_traceSegment_078_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_078 2160 540 = [13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2160 270 270, g32p_row03_traceSegment_078_2160_0270, g32p_row03_traceSegment_078_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 2700 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2724 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2716 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2716 8 9, g32p_row03_traceSegment_078_2716_0008, g32p_row03_traceSegment_078_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 2700 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2700 16 17, g32p_row03_traceSegment_078_2700_0016, g32p_row03_traceSegment_078_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2733 8 9, g32p_row03_traceSegment_078_2733_0008, g32p_row03_traceSegment_078_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2750 8 9, g32p_row03_traceSegment_078_2750_0008, g32p_row03_traceSegment_078_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2733 17 17, g32p_row03_traceSegment_078_2733_0017, g32p_row03_traceSegment_078_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 2700 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2700 33 34, g32p_row03_traceSegment_078_2700_0033, g32p_row03_traceSegment_078_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2767 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2767 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2767 8 9, g32p_row03_traceSegment_078_2767_0008, g32p_row03_traceSegment_078_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2784 8 9, g32p_row03_traceSegment_078_2784_0008, g32p_row03_traceSegment_078_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2767 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2767 17 17, g32p_row03_traceSegment_078_2767_0017, g32p_row03_traceSegment_078_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2801 8 9, g32p_row03_traceSegment_078_2801_0008, g32p_row03_traceSegment_078_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2818 8 9, g32p_row03_traceSegment_078_2818_0008, g32p_row03_traceSegment_078_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2801 17 17, g32p_row03_traceSegment_078_2801_0017, g32p_row03_traceSegment_078_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 2767 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2767 34 34, g32p_row03_traceSegment_078_2767_0034, g32p_row03_traceSegment_078_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 2700 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2700 67 68, g32p_row03_traceSegment_078_2700_0067, g32p_row03_traceSegment_078_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2851 8 9, g32p_row03_traceSegment_078_2851_0008, g32p_row03_traceSegment_078_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2835 16 17, g32p_row03_traceSegment_078_2835_0016, g32p_row03_traceSegment_078_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2868 8 9, g32p_row03_traceSegment_078_2868_0008, g32p_row03_traceSegment_078_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2885 8 9, g32p_row03_traceSegment_078_2885_0008, g32p_row03_traceSegment_078_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2868 17 17, g32p_row03_traceSegment_078_2868_0017, g32p_row03_traceSegment_078_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2835 33 34, g32p_row03_traceSegment_078_2835_0033, g32p_row03_traceSegment_078_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2902 8 9, g32p_row03_traceSegment_078_2902_0008, g32p_row03_traceSegment_078_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2919 8 9, g32p_row03_traceSegment_078_2919_0008, g32p_row03_traceSegment_078_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2902 17 17, g32p_row03_traceSegment_078_2902_0017, g32p_row03_traceSegment_078_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2936 8 9, g32p_row03_traceSegment_078_2936_0008, g32p_row03_traceSegment_078_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2953 8 9, g32p_row03_traceSegment_078_2953_0008, g32p_row03_traceSegment_078_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2936 17 17, g32p_row03_traceSegment_078_2936_0017, g32p_row03_traceSegment_078_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2902 34 34, g32p_row03_traceSegment_078_2902_0034, g32p_row03_traceSegment_078_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2835 67 68, g32p_row03_traceSegment_078_2835_0067, g32p_row03_traceSegment_078_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 2700 270 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2700 135 135, g32p_row03_traceSegment_078_2700_0135, g32p_row03_traceSegment_078_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2986 8 9, g32p_row03_traceSegment_078_2986_0008, g32p_row03_traceSegment_078_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2970 16 17, g32p_row03_traceSegment_078_2970_0016, g32p_row03_traceSegment_078_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3003 8 9, g32p_row03_traceSegment_078_3003_0008, g32p_row03_traceSegment_078_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3020 8 9, g32p_row03_traceSegment_078_3020_0008, g32p_row03_traceSegment_078_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3003 17 17, g32p_row03_traceSegment_078_3003_0017, g32p_row03_traceSegment_078_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2970 33 34, g32p_row03_traceSegment_078_2970_0033, g32p_row03_traceSegment_078_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3037 8 9, g32p_row03_traceSegment_078_3037_0008, g32p_row03_traceSegment_078_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3054 8 9, g32p_row03_traceSegment_078_3054_0008, g32p_row03_traceSegment_078_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3037 17 17, g32p_row03_traceSegment_078_3037_0017, g32p_row03_traceSegment_078_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3071 8 9, g32p_row03_traceSegment_078_3071_0008, g32p_row03_traceSegment_078_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3088 8 9, g32p_row03_traceSegment_078_3088_0008, g32p_row03_traceSegment_078_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3071 17 17, g32p_row03_traceSegment_078_3071_0017, g32p_row03_traceSegment_078_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3037 34 34, g32p_row03_traceSegment_078_3037_0034, g32p_row03_traceSegment_078_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2970 67 68, g32p_row03_traceSegment_078_2970_0067, g32p_row03_traceSegment_078_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3121 8 9, g32p_row03_traceSegment_078_3121_0008, g32p_row03_traceSegment_078_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3105 16 17, g32p_row03_traceSegment_078_3105_0016, g32p_row03_traceSegment_078_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3138 8 9, g32p_row03_traceSegment_078_3138_0008, g32p_row03_traceSegment_078_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3155 8 9, g32p_row03_traceSegment_078_3155_0008, g32p_row03_traceSegment_078_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3138 17 17, g32p_row03_traceSegment_078_3138_0017, g32p_row03_traceSegment_078_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3105 33 34, g32p_row03_traceSegment_078_3105_0033, g32p_row03_traceSegment_078_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3172 8 9, g32p_row03_traceSegment_078_3172_0008, g32p_row03_traceSegment_078_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3189 8 9, g32p_row03_traceSegment_078_3189_0008, g32p_row03_traceSegment_078_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3172 17 17, g32p_row03_traceSegment_078_3172_0017, g32p_row03_traceSegment_078_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3206 8 9, g32p_row03_traceSegment_078_3206_0008, g32p_row03_traceSegment_078_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3223 8 9, g32p_row03_traceSegment_078_3223_0008, g32p_row03_traceSegment_078_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3206 17 17, g32p_row03_traceSegment_078_3206_0017, g32p_row03_traceSegment_078_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3172 34 34, g32p_row03_traceSegment_078_3172_0034, g32p_row03_traceSegment_078_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3105 67 68, g32p_row03_traceSegment_078_3105_0067, g32p_row03_traceSegment_078_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2970 135 135, g32p_row03_traceSegment_078_2970_0135, g32p_row03_traceSegment_078_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_078 2700 540 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2700 270 270, g32p_row03_traceSegment_078_2700_0270, g32p_row03_traceSegment_078_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_078 2160 1080 = [17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2160 540 540, g32p_row03_traceSegment_078_2160_0540, g32p_row03_traceSegment_078_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3256 8 9, g32p_row03_traceSegment_078_3256_0008, g32p_row03_traceSegment_078_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3240 16 17, g32p_row03_traceSegment_078_3240_0016, g32p_row03_traceSegment_078_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3273 8 9, g32p_row03_traceSegment_078_3273_0008, g32p_row03_traceSegment_078_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3290 8 9, g32p_row03_traceSegment_078_3290_0008, g32p_row03_traceSegment_078_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3273 17 17, g32p_row03_traceSegment_078_3273_0017, g32p_row03_traceSegment_078_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3240 33 34, g32p_row03_traceSegment_078_3240_0033, g32p_row03_traceSegment_078_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3307 8 9, g32p_row03_traceSegment_078_3307_0008, g32p_row03_traceSegment_078_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3324 8 9, g32p_row03_traceSegment_078_3324_0008, g32p_row03_traceSegment_078_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3307 17 17, g32p_row03_traceSegment_078_3307_0017, g32p_row03_traceSegment_078_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3341 8 9, g32p_row03_traceSegment_078_3341_0008, g32p_row03_traceSegment_078_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3358 8 9, g32p_row03_traceSegment_078_3358_0008, g32p_row03_traceSegment_078_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3341 17 17, g32p_row03_traceSegment_078_3341_0017, g32p_row03_traceSegment_078_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3307 34 34, g32p_row03_traceSegment_078_3307_0034, g32p_row03_traceSegment_078_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3240 67 68, g32p_row03_traceSegment_078_3240_0067, g32p_row03_traceSegment_078_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3391 8 9, g32p_row03_traceSegment_078_3391_0008, g32p_row03_traceSegment_078_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3375 16 17, g32p_row03_traceSegment_078_3375_0016, g32p_row03_traceSegment_078_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3408 8 9, g32p_row03_traceSegment_078_3408_0008, g32p_row03_traceSegment_078_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3425 8 9, g32p_row03_traceSegment_078_3425_0008, g32p_row03_traceSegment_078_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3408 17 17, g32p_row03_traceSegment_078_3408_0017, g32p_row03_traceSegment_078_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3375 33 34, g32p_row03_traceSegment_078_3375_0033, g32p_row03_traceSegment_078_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3442 8 9, g32p_row03_traceSegment_078_3442_0008, g32p_row03_traceSegment_078_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3459 8 9, g32p_row03_traceSegment_078_3459_0008, g32p_row03_traceSegment_078_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3442 17 17, g32p_row03_traceSegment_078_3442_0017, g32p_row03_traceSegment_078_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3476 8 9, g32p_row03_traceSegment_078_3476_0008, g32p_row03_traceSegment_078_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3493 8 9, g32p_row03_traceSegment_078_3493_0008, g32p_row03_traceSegment_078_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3476 17 17, g32p_row03_traceSegment_078_3476_0017, g32p_row03_traceSegment_078_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3442 34 34, g32p_row03_traceSegment_078_3442_0034, g32p_row03_traceSegment_078_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3375 67 68, g32p_row03_traceSegment_078_3375_0067, g32p_row03_traceSegment_078_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3240 135 135, g32p_row03_traceSegment_078_3240_0135, g32p_row03_traceSegment_078_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3526 8 9, g32p_row03_traceSegment_078_3526_0008, g32p_row03_traceSegment_078_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3510 16 17, g32p_row03_traceSegment_078_3510_0016, g32p_row03_traceSegment_078_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3543 8 9, g32p_row03_traceSegment_078_3543_0008, g32p_row03_traceSegment_078_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3560 8 9, g32p_row03_traceSegment_078_3560_0008, g32p_row03_traceSegment_078_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3543 17 17, g32p_row03_traceSegment_078_3543_0017, g32p_row03_traceSegment_078_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3510 33 34, g32p_row03_traceSegment_078_3510_0033, g32p_row03_traceSegment_078_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3577 8 9, g32p_row03_traceSegment_078_3577_0008, g32p_row03_traceSegment_078_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3594 8 9, g32p_row03_traceSegment_078_3594_0008, g32p_row03_traceSegment_078_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3577 17 17, g32p_row03_traceSegment_078_3577_0017, g32p_row03_traceSegment_078_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3611 8 9, g32p_row03_traceSegment_078_3611_0008, g32p_row03_traceSegment_078_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3628 8 9, g32p_row03_traceSegment_078_3628_0008, g32p_row03_traceSegment_078_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3611 17 17, g32p_row03_traceSegment_078_3611_0017, g32p_row03_traceSegment_078_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3577 34 34, g32p_row03_traceSegment_078_3577_0034, g32p_row03_traceSegment_078_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3510 67 68, g32p_row03_traceSegment_078_3510_0067, g32p_row03_traceSegment_078_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3661 8 9, g32p_row03_traceSegment_078_3661_0008, g32p_row03_traceSegment_078_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3645 16 17, g32p_row03_traceSegment_078_3645_0016, g32p_row03_traceSegment_078_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3678 8 9, g32p_row03_traceSegment_078_3678_0008, g32p_row03_traceSegment_078_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3695 8 9, g32p_row03_traceSegment_078_3695_0008, g32p_row03_traceSegment_078_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3678 17 17, g32p_row03_traceSegment_078_3678_0017, g32p_row03_traceSegment_078_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3645 33 34, g32p_row03_traceSegment_078_3645_0033, g32p_row03_traceSegment_078_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3712 8 9, g32p_row03_traceSegment_078_3712_0008, g32p_row03_traceSegment_078_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3729 8 9, g32p_row03_traceSegment_078_3729_0008, g32p_row03_traceSegment_078_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3712 17 17, g32p_row03_traceSegment_078_3712_0017, g32p_row03_traceSegment_078_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3746 8 9, g32p_row03_traceSegment_078_3746_0008, g32p_row03_traceSegment_078_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3763 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3771 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3763 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3763 8 9, g32p_row03_traceSegment_078_3763_0008, g32p_row03_traceSegment_078_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3746 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3746 17 17, g32p_row03_traceSegment_078_3746_0017, g32p_row03_traceSegment_078_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 3712 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3712 34 34, g32p_row03_traceSegment_078_3712_0034, g32p_row03_traceSegment_078_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 3645 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3645 67 68, g32p_row03_traceSegment_078_3645_0067, g32p_row03_traceSegment_078_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 3510 270 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3510 135 135, g32p_row03_traceSegment_078_3510_0135, g32p_row03_traceSegment_078_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_078 3240 540 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3240 270 270, g32p_row03_traceSegment_078_3240_0270, g32p_row03_traceSegment_078_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3796 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3796 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3796 8 9, g32p_row03_traceSegment_078_3796_0008, g32p_row03_traceSegment_078_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 3780 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3780 16 17, g32p_row03_traceSegment_078_3780_0016, g32p_row03_traceSegment_078_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3821 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3813 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3813 8 9, g32p_row03_traceSegment_078_3813_0008, g32p_row03_traceSegment_078_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3830 8 9, g32p_row03_traceSegment_078_3830_0008, g32p_row03_traceSegment_078_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3813 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3813 17 17, g32p_row03_traceSegment_078_3813_0017, g32p_row03_traceSegment_078_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 3780 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3780 33 34, g32p_row03_traceSegment_078_3780_0033, g32p_row03_traceSegment_078_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3847 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3855 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3847 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3847 8 9, g32p_row03_traceSegment_078_3847_0008, g32p_row03_traceSegment_078_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3864 8 9, g32p_row03_traceSegment_078_3864_0008, g32p_row03_traceSegment_078_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3847 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3847 17 17, g32p_row03_traceSegment_078_3847_0017, g32p_row03_traceSegment_078_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3881 8 9, g32p_row03_traceSegment_078_3881_0008, g32p_row03_traceSegment_078_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3898 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3898 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3898 8 9, g32p_row03_traceSegment_078_3898_0008, g32p_row03_traceSegment_078_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3881 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3881 17 17, g32p_row03_traceSegment_078_3881_0017, g32p_row03_traceSegment_078_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 3847 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3847 34 34, g32p_row03_traceSegment_078_3847_0034, g32p_row03_traceSegment_078_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 3780 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3780 67 68, g32p_row03_traceSegment_078_3780_0067, g32p_row03_traceSegment_078_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 3915 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3939 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3931 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3931 8 9, g32p_row03_traceSegment_078_3931_0008, g32p_row03_traceSegment_078_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 3915 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3915 16 17, g32p_row03_traceSegment_078_3915_0016, g32p_row03_traceSegment_078_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3948 8 9, g32p_row03_traceSegment_078_3948_0008, g32p_row03_traceSegment_078_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3965 8 9, g32p_row03_traceSegment_078_3965_0008, g32p_row03_traceSegment_078_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3948 17 17, g32p_row03_traceSegment_078_3948_0017, g32p_row03_traceSegment_078_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 3915 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3915 33 34, g32p_row03_traceSegment_078_3915_0033, g32p_row03_traceSegment_078_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3982 8 9, g32p_row03_traceSegment_078_3982_0008, g32p_row03_traceSegment_078_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 3999 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 3999 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3999 8 9, g32p_row03_traceSegment_078_3999_0008, g32p_row03_traceSegment_078_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 3982 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3982 17 17, g32p_row03_traceSegment_078_3982_0017, g32p_row03_traceSegment_078_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4016 8 9, g32p_row03_traceSegment_078_4016_0008, g32p_row03_traceSegment_078_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4033 8 9, g32p_row03_traceSegment_078_4033_0008, g32p_row03_traceSegment_078_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4016 17 17, g32p_row03_traceSegment_078_4016_0017, g32p_row03_traceSegment_078_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 3982 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3982 34 34, g32p_row03_traceSegment_078_3982_0034, g32p_row03_traceSegment_078_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 3915 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3915 67 68, g32p_row03_traceSegment_078_3915_0067, g32p_row03_traceSegment_078_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 3780 270 = [9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3780 135 135, g32p_row03_traceSegment_078_3780_0135, g32p_row03_traceSegment_078_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 4050 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4066 8 9, g32p_row03_traceSegment_078_4066_0008, g32p_row03_traceSegment_078_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 4050 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4050 16 17, g32p_row03_traceSegment_078_4050_0016, g32p_row03_traceSegment_078_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4083 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4083 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4083 8 9, g32p_row03_traceSegment_078_4083_0008, g32p_row03_traceSegment_078_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4100 8 9, g32p_row03_traceSegment_078_4100_0008, g32p_row03_traceSegment_078_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 4083 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4083 17 17, g32p_row03_traceSegment_078_4083_0017, g32p_row03_traceSegment_078_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 4050 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4050 33 34, g32p_row03_traceSegment_078_4050_0033, g32p_row03_traceSegment_078_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4117 8 9, g32p_row03_traceSegment_078_4117_0008, g32p_row03_traceSegment_078_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4134 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4134 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4134 8 9, g32p_row03_traceSegment_078_4134_0008, g32p_row03_traceSegment_078_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 4117 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4117 17 17, g32p_row03_traceSegment_078_4117_0017, g32p_row03_traceSegment_078_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4151 8 9, g32p_row03_traceSegment_078_4151_0008, g32p_row03_traceSegment_078_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4168 8 9, g32p_row03_traceSegment_078_4168_0008, g32p_row03_traceSegment_078_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4151 17 17, g32p_row03_traceSegment_078_4151_0017, g32p_row03_traceSegment_078_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 4117 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4117 34 34, g32p_row03_traceSegment_078_4117_0034, g32p_row03_traceSegment_078_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 4050 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4050 67 68, g32p_row03_traceSegment_078_4050_0067, g32p_row03_traceSegment_078_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_078 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4201 8 9, g32p_row03_traceSegment_078_4201_0008, g32p_row03_traceSegment_078_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_078 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4185 16 17, g32p_row03_traceSegment_078_4185_0016, g32p_row03_traceSegment_078_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4218 8 9, g32p_row03_traceSegment_078_4218_0008, g32p_row03_traceSegment_078_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4235 8 9, g32p_row03_traceSegment_078_4235_0008, g32p_row03_traceSegment_078_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4218 17 17, g32p_row03_traceSegment_078_4218_0017, g32p_row03_traceSegment_078_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_078 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4185 33 34, g32p_row03_traceSegment_078_4185_0033, g32p_row03_traceSegment_078_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4252 8 9, g32p_row03_traceSegment_078_4252_0008, g32p_row03_traceSegment_078_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4269 8 9, g32p_row03_traceSegment_078_4269_0008, g32p_row03_traceSegment_078_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4252 17 17, g32p_row03_traceSegment_078_4252_0017, g32p_row03_traceSegment_078_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4294 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4286 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4286 8 9, g32p_row03_traceSegment_078_4286_0008, g32p_row03_traceSegment_078_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_078 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_078 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_078_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_078 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4303 8 9, g32p_row03_traceSegment_078_4303_0008, g32p_row03_traceSegment_078_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_078 4286 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4286 17 17, g32p_row03_traceSegment_078_4286_0017, g32p_row03_traceSegment_078_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_078 4252 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4252 34 34, g32p_row03_traceSegment_078_4252_0034, g32p_row03_traceSegment_078_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_078 4185 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4185 67 68, g32p_row03_traceSegment_078_4185_0067, g32p_row03_traceSegment_078_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_078_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_078 4050 270 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 4050 135 135, g32p_row03_traceSegment_078_4050_0135, g32p_row03_traceSegment_078_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_078 3780 540 = [13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3780 270 270, g32p_row03_traceSegment_078_3780_0270, g32p_row03_traceSegment_078_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_078_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_078 3240 1080 = [15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 3240 540 540, g32p_row03_traceSegment_078_3240_0540, g32p_row03_traceSegment_078_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_078_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_078 2160 2160 = [32] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 2160 1080 1080, g32p_row03_traceSegment_078_2160_1080, g32p_row03_traceSegment_078_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_078_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_078 0 4320 = [40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_078 0 2160 2160, g32p_row03_traceSegment_078_0000_2160, g32p_row03_traceSegment_078_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 78 = [40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_078_0000_4320

end HodgeLean.Foundations.Program

end
end
