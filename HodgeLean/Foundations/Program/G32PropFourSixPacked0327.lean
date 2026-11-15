import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_060 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 60 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_060_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 16 8 9, g32p_row03_traceSegment_060_0016_0008, g32p_row03_traceSegment_060_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 0 16 17, g32p_row03_traceSegment_060_0000_0016, g32p_row03_traceSegment_060_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 33 8 9, g32p_row03_traceSegment_060_0033_0008, g32p_row03_traceSegment_060_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 50 8 9, g32p_row03_traceSegment_060_0050_0008, g32p_row03_traceSegment_060_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 33 17 17, g32p_row03_traceSegment_060_0033_0017, g32p_row03_traceSegment_060_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 0 33 34, g32p_row03_traceSegment_060_0000_0033, g32p_row03_traceSegment_060_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 67 8 9, g32p_row03_traceSegment_060_0067_0008, g32p_row03_traceSegment_060_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 84 8 9, g32p_row03_traceSegment_060_0084_0008, g32p_row03_traceSegment_060_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 67 17 17, g32p_row03_traceSegment_060_0067_0017, g32p_row03_traceSegment_060_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 101 8 9, g32p_row03_traceSegment_060_0101_0008, g32p_row03_traceSegment_060_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 118 8 9, g32p_row03_traceSegment_060_0118_0008, g32p_row03_traceSegment_060_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 101 17 17, g32p_row03_traceSegment_060_0101_0017, g32p_row03_traceSegment_060_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 67 34 34, g32p_row03_traceSegment_060_0067_0034, g32p_row03_traceSegment_060_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 0 67 68, g32p_row03_traceSegment_060_0000_0067, g32p_row03_traceSegment_060_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 151 8 9, g32p_row03_traceSegment_060_0151_0008, g32p_row03_traceSegment_060_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 135 16 17, g32p_row03_traceSegment_060_0135_0016, g32p_row03_traceSegment_060_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 168 8 9, g32p_row03_traceSegment_060_0168_0008, g32p_row03_traceSegment_060_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 185 8 9, g32p_row03_traceSegment_060_0185_0008, g32p_row03_traceSegment_060_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 168 17 17, g32p_row03_traceSegment_060_0168_0017, g32p_row03_traceSegment_060_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 135 33 34, g32p_row03_traceSegment_060_0135_0033, g32p_row03_traceSegment_060_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 202 8 9, g32p_row03_traceSegment_060_0202_0008, g32p_row03_traceSegment_060_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 219 8 9, g32p_row03_traceSegment_060_0219_0008, g32p_row03_traceSegment_060_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 202 17 17, g32p_row03_traceSegment_060_0202_0017, g32p_row03_traceSegment_060_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 236 8 9, g32p_row03_traceSegment_060_0236_0008, g32p_row03_traceSegment_060_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 253 8 9, g32p_row03_traceSegment_060_0253_0008, g32p_row03_traceSegment_060_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 236 17 17, g32p_row03_traceSegment_060_0236_0017, g32p_row03_traceSegment_060_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 202 34 34, g32p_row03_traceSegment_060_0202_0034, g32p_row03_traceSegment_060_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 135 67 68, g32p_row03_traceSegment_060_0135_0067, g32p_row03_traceSegment_060_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 0 135 135, g32p_row03_traceSegment_060_0000_0135, g32p_row03_traceSegment_060_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 286 8 9, g32p_row03_traceSegment_060_0286_0008, g32p_row03_traceSegment_060_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 270 16 17, g32p_row03_traceSegment_060_0270_0016, g32p_row03_traceSegment_060_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 303 8 9, g32p_row03_traceSegment_060_0303_0008, g32p_row03_traceSegment_060_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 320 8 9, g32p_row03_traceSegment_060_0320_0008, g32p_row03_traceSegment_060_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 303 17 17, g32p_row03_traceSegment_060_0303_0017, g32p_row03_traceSegment_060_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 270 33 34, g32p_row03_traceSegment_060_0270_0033, g32p_row03_traceSegment_060_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 337 8 9, g32p_row03_traceSegment_060_0337_0008, g32p_row03_traceSegment_060_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 354 8 9, g32p_row03_traceSegment_060_0354_0008, g32p_row03_traceSegment_060_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 337 17 17, g32p_row03_traceSegment_060_0337_0017, g32p_row03_traceSegment_060_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 371 8 9, g32p_row03_traceSegment_060_0371_0008, g32p_row03_traceSegment_060_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 388 8 9, g32p_row03_traceSegment_060_0388_0008, g32p_row03_traceSegment_060_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 371 17 17, g32p_row03_traceSegment_060_0371_0017, g32p_row03_traceSegment_060_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 337 34 34, g32p_row03_traceSegment_060_0337_0034, g32p_row03_traceSegment_060_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 270 67 68, g32p_row03_traceSegment_060_0270_0067, g32p_row03_traceSegment_060_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 421 8 9, g32p_row03_traceSegment_060_0421_0008, g32p_row03_traceSegment_060_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 405 16 17, g32p_row03_traceSegment_060_0405_0016, g32p_row03_traceSegment_060_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 446 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 438 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 438 8 9, g32p_row03_traceSegment_060_0438_0008, g32p_row03_traceSegment_060_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 455 8 9, g32p_row03_traceSegment_060_0455_0008, g32p_row03_traceSegment_060_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 438 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 438 17 17, g32p_row03_traceSegment_060_0438_0017, g32p_row03_traceSegment_060_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 405 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 405 33 34, g32p_row03_traceSegment_060_0405_0033, g32p_row03_traceSegment_060_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 472 8 9, g32p_row03_traceSegment_060_0472_0008, g32p_row03_traceSegment_060_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 489 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 489 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 489 8 9, g32p_row03_traceSegment_060_0489_0008, g32p_row03_traceSegment_060_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 472 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 472 17 17, g32p_row03_traceSegment_060_0472_0017, g32p_row03_traceSegment_060_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 514 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 506 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 506 8 9, g32p_row03_traceSegment_060_0506_0008, g32p_row03_traceSegment_060_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 523 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 523 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 523 8 9, g32p_row03_traceSegment_060_0523_0008, g32p_row03_traceSegment_060_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 506 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 506 17 17, g32p_row03_traceSegment_060_0506_0017, g32p_row03_traceSegment_060_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 472 68 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 472 34 34, g32p_row03_traceSegment_060_0472_0034, g32p_row03_traceSegment_060_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 405 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 405 67 68, g32p_row03_traceSegment_060_0405_0067, g32p_row03_traceSegment_060_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 270 270 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 270 135 135, g32p_row03_traceSegment_060_0270_0135, g32p_row03_traceSegment_060_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_060 0 540 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 0 270 270, g32p_row03_traceSegment_060_0000_0270, g32p_row03_traceSegment_060_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 556 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 564 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 556 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 556 8 9, g32p_row03_traceSegment_060_0556_0008, g32p_row03_traceSegment_060_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 540 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 540 16 17, g32p_row03_traceSegment_060_0540_0016, g32p_row03_traceSegment_060_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 573 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 581 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 573 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 573 8 9, g32p_row03_traceSegment_060_0573_0008, g32p_row03_traceSegment_060_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 590 8 9, g32p_row03_traceSegment_060_0590_0008, g32p_row03_traceSegment_060_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 573 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 573 17 17, g32p_row03_traceSegment_060_0573_0017, g32p_row03_traceSegment_060_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 540 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 540 33 34, g32p_row03_traceSegment_060_0540_0033, g32p_row03_traceSegment_060_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 607 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 615 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 607 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 607 8 9, g32p_row03_traceSegment_060_0607_0008, g32p_row03_traceSegment_060_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 624 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 624 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 624 8 9, g32p_row03_traceSegment_060_0624_0008, g32p_row03_traceSegment_060_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 607 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 607 17 17, g32p_row03_traceSegment_060_0607_0017, g32p_row03_traceSegment_060_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 641 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 641 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 641 8 9, g32p_row03_traceSegment_060_0641_0008, g32p_row03_traceSegment_060_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 658 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 658 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 658 8 9, g32p_row03_traceSegment_060_0658_0008, g32p_row03_traceSegment_060_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 641 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 641 17 17, g32p_row03_traceSegment_060_0641_0017, g32p_row03_traceSegment_060_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 607 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 607 34 34, g32p_row03_traceSegment_060_0607_0034, g32p_row03_traceSegment_060_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 540 135 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 540 67 68, g32p_row03_traceSegment_060_0540_0067, g32p_row03_traceSegment_060_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 675 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 691 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 699 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 691 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 691 8 9, g32p_row03_traceSegment_060_0691_0008, g32p_row03_traceSegment_060_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 675 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 675 16 17, g32p_row03_traceSegment_060_0675_0016, g32p_row03_traceSegment_060_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 708 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 708 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 708 8 9, g32p_row03_traceSegment_060_0708_0008, g32p_row03_traceSegment_060_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 725 8 9, g32p_row03_traceSegment_060_0725_0008, g32p_row03_traceSegment_060_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 708 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 708 17 17, g32p_row03_traceSegment_060_0708_0017, g32p_row03_traceSegment_060_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 675 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 675 33 34, g32p_row03_traceSegment_060_0675_0033, g32p_row03_traceSegment_060_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 742 8 9, g32p_row03_traceSegment_060_0742_0008, g32p_row03_traceSegment_060_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 759 8 9, g32p_row03_traceSegment_060_0759_0008, g32p_row03_traceSegment_060_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 742 17 17, g32p_row03_traceSegment_060_0742_0017, g32p_row03_traceSegment_060_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 776 8 9, g32p_row03_traceSegment_060_0776_0008, g32p_row03_traceSegment_060_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 793 8 9, g32p_row03_traceSegment_060_0793_0008, g32p_row03_traceSegment_060_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 776 17 17, g32p_row03_traceSegment_060_0776_0017, g32p_row03_traceSegment_060_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 742 34 34, g32p_row03_traceSegment_060_0742_0034, g32p_row03_traceSegment_060_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 675 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 675 67 68, g32p_row03_traceSegment_060_0675_0067, g32p_row03_traceSegment_060_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 540 270 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 540 135 135, g32p_row03_traceSegment_060_0540_0135, g32p_row03_traceSegment_060_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 826 8 9, g32p_row03_traceSegment_060_0826_0008, g32p_row03_traceSegment_060_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 810 16 17, g32p_row03_traceSegment_060_0810_0016, g32p_row03_traceSegment_060_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 843 8 9, g32p_row03_traceSegment_060_0843_0008, g32p_row03_traceSegment_060_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 860 8 9, g32p_row03_traceSegment_060_0860_0008, g32p_row03_traceSegment_060_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 843 17 17, g32p_row03_traceSegment_060_0843_0017, g32p_row03_traceSegment_060_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 810 33 34, g32p_row03_traceSegment_060_0810_0033, g32p_row03_traceSegment_060_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 877 8 9, g32p_row03_traceSegment_060_0877_0008, g32p_row03_traceSegment_060_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 894 8 9, g32p_row03_traceSegment_060_0894_0008, g32p_row03_traceSegment_060_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 877 17 17, g32p_row03_traceSegment_060_0877_0017, g32p_row03_traceSegment_060_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 911 8 9, g32p_row03_traceSegment_060_0911_0008, g32p_row03_traceSegment_060_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 928 8 9, g32p_row03_traceSegment_060_0928_0008, g32p_row03_traceSegment_060_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 911 17 17, g32p_row03_traceSegment_060_0911_0017, g32p_row03_traceSegment_060_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 877 34 34, g32p_row03_traceSegment_060_0877_0034, g32p_row03_traceSegment_060_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 810 67 68, g32p_row03_traceSegment_060_0810_0067, g32p_row03_traceSegment_060_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 961 8 9, g32p_row03_traceSegment_060_0961_0008, g32p_row03_traceSegment_060_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 945 16 17, g32p_row03_traceSegment_060_0945_0016, g32p_row03_traceSegment_060_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 978 8 9, g32p_row03_traceSegment_060_0978_0008, g32p_row03_traceSegment_060_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 995 8 9, g32p_row03_traceSegment_060_0995_0008, g32p_row03_traceSegment_060_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 978 17 17, g32p_row03_traceSegment_060_0978_0017, g32p_row03_traceSegment_060_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 945 33 34, g32p_row03_traceSegment_060_0945_0033, g32p_row03_traceSegment_060_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1012 8 9, g32p_row03_traceSegment_060_1012_0008, g32p_row03_traceSegment_060_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1029 8 9, g32p_row03_traceSegment_060_1029_0008, g32p_row03_traceSegment_060_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1012 17 17, g32p_row03_traceSegment_060_1012_0017, g32p_row03_traceSegment_060_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1046 8 9, g32p_row03_traceSegment_060_1046_0008, g32p_row03_traceSegment_060_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1063 8 9, g32p_row03_traceSegment_060_1063_0008, g32p_row03_traceSegment_060_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1046 17 17, g32p_row03_traceSegment_060_1046_0017, g32p_row03_traceSegment_060_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1012 34 34, g32p_row03_traceSegment_060_1012_0034, g32p_row03_traceSegment_060_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 945 67 68, g32p_row03_traceSegment_060_0945_0067, g32p_row03_traceSegment_060_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 810 135 135, g32p_row03_traceSegment_060_0810_0135, g32p_row03_traceSegment_060_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_060 540 540 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 540 270 270, g32p_row03_traceSegment_060_0540_0270, g32p_row03_traceSegment_060_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_060 0 1080 = [0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 0 540 540, g32p_row03_traceSegment_060_0000_0540, g32p_row03_traceSegment_060_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1096 8 9, g32p_row03_traceSegment_060_1096_0008, g32p_row03_traceSegment_060_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1080 16 17, g32p_row03_traceSegment_060_1080_0016, g32p_row03_traceSegment_060_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1113 8 9, g32p_row03_traceSegment_060_1113_0008, g32p_row03_traceSegment_060_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1130 8 9, g32p_row03_traceSegment_060_1130_0008, g32p_row03_traceSegment_060_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1113 17 17, g32p_row03_traceSegment_060_1113_0017, g32p_row03_traceSegment_060_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1080 33 34, g32p_row03_traceSegment_060_1080_0033, g32p_row03_traceSegment_060_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1147 8 9, g32p_row03_traceSegment_060_1147_0008, g32p_row03_traceSegment_060_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1164 8 9, g32p_row03_traceSegment_060_1164_0008, g32p_row03_traceSegment_060_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1147 17 17, g32p_row03_traceSegment_060_1147_0017, g32p_row03_traceSegment_060_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1181 8 9, g32p_row03_traceSegment_060_1181_0008, g32p_row03_traceSegment_060_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1198 8 9, g32p_row03_traceSegment_060_1198_0008, g32p_row03_traceSegment_060_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1181 17 17, g32p_row03_traceSegment_060_1181_0017, g32p_row03_traceSegment_060_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1147 34 34, g32p_row03_traceSegment_060_1147_0034, g32p_row03_traceSegment_060_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1080 67 68, g32p_row03_traceSegment_060_1080_0067, g32p_row03_traceSegment_060_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1231 8 9, g32p_row03_traceSegment_060_1231_0008, g32p_row03_traceSegment_060_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1215 16 17, g32p_row03_traceSegment_060_1215_0016, g32p_row03_traceSegment_060_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1248 8 9, g32p_row03_traceSegment_060_1248_0008, g32p_row03_traceSegment_060_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1265 8 9, g32p_row03_traceSegment_060_1265_0008, g32p_row03_traceSegment_060_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1248 17 17, g32p_row03_traceSegment_060_1248_0017, g32p_row03_traceSegment_060_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1215 33 34, g32p_row03_traceSegment_060_1215_0033, g32p_row03_traceSegment_060_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1282 8 9, g32p_row03_traceSegment_060_1282_0008, g32p_row03_traceSegment_060_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1299 8 9, g32p_row03_traceSegment_060_1299_0008, g32p_row03_traceSegment_060_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1282 17 17, g32p_row03_traceSegment_060_1282_0017, g32p_row03_traceSegment_060_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1324 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1316 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1316 8 9, g32p_row03_traceSegment_060_1316_0008, g32p_row03_traceSegment_060_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1333 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1333 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1333 8 9, g32p_row03_traceSegment_060_1333_0008, g32p_row03_traceSegment_060_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1316 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1316 17 17, g32p_row03_traceSegment_060_1316_0017, g32p_row03_traceSegment_060_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 1282 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1282 34 34, g32p_row03_traceSegment_060_1282_0034, g32p_row03_traceSegment_060_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 1215 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1215 67 68, g32p_row03_traceSegment_060_1215_0067, g32p_row03_traceSegment_060_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 1080 270 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1080 135 135, g32p_row03_traceSegment_060_1080_0135, g32p_row03_traceSegment_060_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 1350 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1366 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1366 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1366 8 9, g32p_row03_traceSegment_060_1366_0008, g32p_row03_traceSegment_060_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 1350 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1350 16 17, g32p_row03_traceSegment_060_1350_0016, g32p_row03_traceSegment_060_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1383 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1383 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1383 8 9, g32p_row03_traceSegment_060_1383_0008, g32p_row03_traceSegment_060_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1408 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1400 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1400 8 9, g32p_row03_traceSegment_060_1400_0008, g32p_row03_traceSegment_060_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1383 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1383 17 17, g32p_row03_traceSegment_060_1383_0017, g32p_row03_traceSegment_060_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 1350 67 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1350 33 34, g32p_row03_traceSegment_060_1350_0033, g32p_row03_traceSegment_060_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1417 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1417 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1417 8 9, g32p_row03_traceSegment_060_1417_0008, g32p_row03_traceSegment_060_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1434 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1442 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1434 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1434 8 9, g32p_row03_traceSegment_060_1434_0008, g32p_row03_traceSegment_060_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1417 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1417 17 17, g32p_row03_traceSegment_060_1417_0017, g32p_row03_traceSegment_060_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1451 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1451 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1451 8 9, g32p_row03_traceSegment_060_1451_0008, g32p_row03_traceSegment_060_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1468 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1468 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1468 8 9, g32p_row03_traceSegment_060_1468_0008, g32p_row03_traceSegment_060_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1451 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1451 17 17, g32p_row03_traceSegment_060_1451_0017, g32p_row03_traceSegment_060_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 1417 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1417 34 34, g32p_row03_traceSegment_060_1417_0034, g32p_row03_traceSegment_060_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 1350 135 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1350 67 68, g32p_row03_traceSegment_060_1350_0067, g32p_row03_traceSegment_060_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1501 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1509 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1501 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1501 8 9, g32p_row03_traceSegment_060_1501_0008, g32p_row03_traceSegment_060_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 1485 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1485 16 17, g32p_row03_traceSegment_060_1485_0016, g32p_row03_traceSegment_060_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1518 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1518 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1518 8 9, g32p_row03_traceSegment_060_1518_0008, g32p_row03_traceSegment_060_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1535 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1543 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1535 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1535 8 9, g32p_row03_traceSegment_060_1535_0008, g32p_row03_traceSegment_060_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1518 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1518 17 17, g32p_row03_traceSegment_060_1518_0017, g32p_row03_traceSegment_060_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 1485 67 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1485 33 34, g32p_row03_traceSegment_060_1485_0033, g32p_row03_traceSegment_060_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1560 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1552 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1552 8 9, g32p_row03_traceSegment_060_1552_0008, g32p_row03_traceSegment_060_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1577 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1569 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1569 8 9, g32p_row03_traceSegment_060_1569_0008, g32p_row03_traceSegment_060_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1552 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1552 17 17, g32p_row03_traceSegment_060_1552_0017, g32p_row03_traceSegment_060_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1586 8 9, g32p_row03_traceSegment_060_1586_0008, g32p_row03_traceSegment_060_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1603 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1611 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1603 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1603 8 9, g32p_row03_traceSegment_060_1603_0008, g32p_row03_traceSegment_060_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1586 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1586 17 17, g32p_row03_traceSegment_060_1586_0017, g32p_row03_traceSegment_060_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 1552 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1552 34 34, g32p_row03_traceSegment_060_1552_0034, g32p_row03_traceSegment_060_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 1485 135 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1485 67 68, g32p_row03_traceSegment_060_1485_0067, g32p_row03_traceSegment_060_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 1350 270 = [0, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1350 135 135, g32p_row03_traceSegment_060_1350_0135, g32p_row03_traceSegment_060_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_060 1080 540 = [0, 0, 0, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1080 270 270, g32p_row03_traceSegment_060_1080_0270, g32p_row03_traceSegment_060_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 1620 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1636 8 9, g32p_row03_traceSegment_060_1636_0008, g32p_row03_traceSegment_060_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 1620 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1620 16 17, g32p_row03_traceSegment_060_1620_0016, g32p_row03_traceSegment_060_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1653 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1653 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1653 8 9, g32p_row03_traceSegment_060_1653_0008, g32p_row03_traceSegment_060_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1670 8 9, g32p_row03_traceSegment_060_1670_0008, g32p_row03_traceSegment_060_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1653 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1653 17 17, g32p_row03_traceSegment_060_1653_0017, g32p_row03_traceSegment_060_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 1620 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1620 33 34, g32p_row03_traceSegment_060_1620_0033, g32p_row03_traceSegment_060_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1687 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1695 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1687 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1687 8 9, g32p_row03_traceSegment_060_1687_0008, g32p_row03_traceSegment_060_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1704 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1712 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1704 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1704 8 9, g32p_row03_traceSegment_060_1704_0008, g32p_row03_traceSegment_060_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1687 34 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1687 17 17, g32p_row03_traceSegment_060_1687_0017, g32p_row03_traceSegment_060_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1721 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1729 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1721 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1721 8 9, g32p_row03_traceSegment_060_1721_0008, g32p_row03_traceSegment_060_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1746 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1738 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1738 8 9, g32p_row03_traceSegment_060_1738_0008, g32p_row03_traceSegment_060_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1721 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1721 17 17, g32p_row03_traceSegment_060_1721_0017, g32p_row03_traceSegment_060_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 1687 68 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1687 34 34, g32p_row03_traceSegment_060_1687_0034, g32p_row03_traceSegment_060_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 1620 135 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1620 67 68, g32p_row03_traceSegment_060_1620_0067, g32p_row03_traceSegment_060_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1771 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1779 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1771 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1771 8 9, g32p_row03_traceSegment_060_1771_0008, g32p_row03_traceSegment_060_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 1755 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1755 16 17, g32p_row03_traceSegment_060_1755_0016, g32p_row03_traceSegment_060_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1788 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1788 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1788 8 9, g32p_row03_traceSegment_060_1788_0008, g32p_row03_traceSegment_060_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1805 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1805 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1805 8 9, g32p_row03_traceSegment_060_1805_0008, g32p_row03_traceSegment_060_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1788 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1788 17 17, g32p_row03_traceSegment_060_1788_0017, g32p_row03_traceSegment_060_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 1755 67 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1755 33 34, g32p_row03_traceSegment_060_1755_0033, g32p_row03_traceSegment_060_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1822 8 9, g32p_row03_traceSegment_060_1822_0008, g32p_row03_traceSegment_060_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1839 8 9, g32p_row03_traceSegment_060_1839_0008, g32p_row03_traceSegment_060_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1822 17 17, g32p_row03_traceSegment_060_1822_0017, g32p_row03_traceSegment_060_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1864 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1856 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1856 8 9, g32p_row03_traceSegment_060_1856_0008, g32p_row03_traceSegment_060_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1873 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1873 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1873 8 9, g32p_row03_traceSegment_060_1873_0008, g32p_row03_traceSegment_060_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1856 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1856 17 17, g32p_row03_traceSegment_060_1856_0017, g32p_row03_traceSegment_060_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 1822 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1822 34 34, g32p_row03_traceSegment_060_1822_0034, g32p_row03_traceSegment_060_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 1755 135 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1755 67 68, g32p_row03_traceSegment_060_1755_0067, g32p_row03_traceSegment_060_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 1620 270 = [0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1620 135 135, g32p_row03_traceSegment_060_1620_0135, g32p_row03_traceSegment_060_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1906 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1914 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1906 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1906 8 9, g32p_row03_traceSegment_060_1906_0008, g32p_row03_traceSegment_060_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 1890 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1890 16 17, g32p_row03_traceSegment_060_1890_0016, g32p_row03_traceSegment_060_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1923 8 9, g32p_row03_traceSegment_060_1923_0008, g32p_row03_traceSegment_060_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1940 8 9, g32p_row03_traceSegment_060_1940_0008, g32p_row03_traceSegment_060_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1923 17 17, g32p_row03_traceSegment_060_1923_0017, g32p_row03_traceSegment_060_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 1890 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1890 33 34, g32p_row03_traceSegment_060_1890_0033, g32p_row03_traceSegment_060_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1957 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1957 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1957 8 9, g32p_row03_traceSegment_060_1957_0008, g32p_row03_traceSegment_060_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1974 8 9, g32p_row03_traceSegment_060_1974_0008, g32p_row03_traceSegment_060_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1957 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1957 17 17, g32p_row03_traceSegment_060_1957_0017, g32p_row03_traceSegment_060_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1991 8 9, g32p_row03_traceSegment_060_1991_0008, g32p_row03_traceSegment_060_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2008 8 9, g32p_row03_traceSegment_060_2008_0008, g32p_row03_traceSegment_060_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1991 17 17, g32p_row03_traceSegment_060_1991_0017, g32p_row03_traceSegment_060_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 1957 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1957 34 34, g32p_row03_traceSegment_060_1957_0034, g32p_row03_traceSegment_060_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 1890 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1890 67 68, g32p_row03_traceSegment_060_1890_0067, g32p_row03_traceSegment_060_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2041 8 9, g32p_row03_traceSegment_060_2041_0008, g32p_row03_traceSegment_060_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2025 16 17, g32p_row03_traceSegment_060_2025_0016, g32p_row03_traceSegment_060_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2058 8 9, g32p_row03_traceSegment_060_2058_0008, g32p_row03_traceSegment_060_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2075 8 9, g32p_row03_traceSegment_060_2075_0008, g32p_row03_traceSegment_060_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2058 17 17, g32p_row03_traceSegment_060_2058_0017, g32p_row03_traceSegment_060_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2025 33 34, g32p_row03_traceSegment_060_2025_0033, g32p_row03_traceSegment_060_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2092 8 9, g32p_row03_traceSegment_060_2092_0008, g32p_row03_traceSegment_060_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2109 8 9, g32p_row03_traceSegment_060_2109_0008, g32p_row03_traceSegment_060_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2092 17 17, g32p_row03_traceSegment_060_2092_0017, g32p_row03_traceSegment_060_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2134 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2126 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2126 8 9, g32p_row03_traceSegment_060_2126_0008, g32p_row03_traceSegment_060_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2143 8 9, g32p_row03_traceSegment_060_2143_0008, g32p_row03_traceSegment_060_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2126 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2126 17 17, g32p_row03_traceSegment_060_2126_0017, g32p_row03_traceSegment_060_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 2092 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2092 34 34, g32p_row03_traceSegment_060_2092_0034, g32p_row03_traceSegment_060_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 2025 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2025 67 68, g32p_row03_traceSegment_060_2025_0067, g32p_row03_traceSegment_060_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 1890 270 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1890 135 135, g32p_row03_traceSegment_060_1890_0135, g32p_row03_traceSegment_060_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_060 1620 540 = [0, 0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1620 270 270, g32p_row03_traceSegment_060_1620_0270, g32p_row03_traceSegment_060_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_060_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_060 1080 1080 = [0, 0, 0, 0, 49] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 1080 540 540, g32p_row03_traceSegment_060_1080_0540, g32p_row03_traceSegment_060_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_060 0 2160 = [0, 0, 0, 0, 67] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 0 1080 1080, g32p_row03_traceSegment_060_0000_1080, g32p_row03_traceSegment_060_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2176 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2176 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2176 8 9, g32p_row03_traceSegment_060_2176_0008, g32p_row03_traceSegment_060_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 2160 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2160 16 17, g32p_row03_traceSegment_060_2160_0016, g32p_row03_traceSegment_060_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2193 8 9, g32p_row03_traceSegment_060_2193_0008, g32p_row03_traceSegment_060_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2210 8 9, g32p_row03_traceSegment_060_2210_0008, g32p_row03_traceSegment_060_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2193 17 17, g32p_row03_traceSegment_060_2193_0017, g32p_row03_traceSegment_060_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 2160 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2160 33 34, g32p_row03_traceSegment_060_2160_0033, g32p_row03_traceSegment_060_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2227 8 9, g32p_row03_traceSegment_060_2227_0008, g32p_row03_traceSegment_060_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2252 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2244 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2244 8 9, g32p_row03_traceSegment_060_2244_0008, g32p_row03_traceSegment_060_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2227 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2227 17 17, g32p_row03_traceSegment_060_2227_0017, g32p_row03_traceSegment_060_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2261 8 9, g32p_row03_traceSegment_060_2261_0008, g32p_row03_traceSegment_060_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2278 8 9, g32p_row03_traceSegment_060_2278_0008, g32p_row03_traceSegment_060_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2261 17 17, g32p_row03_traceSegment_060_2261_0017, g32p_row03_traceSegment_060_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 2227 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2227 34 34, g32p_row03_traceSegment_060_2227_0034, g32p_row03_traceSegment_060_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 2160 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2160 67 68, g32p_row03_traceSegment_060_2160_0067, g32p_row03_traceSegment_060_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2319 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2311 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2311 8 9, g32p_row03_traceSegment_060_2311_0008, g32p_row03_traceSegment_060_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 2295 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2295 16 17, g32p_row03_traceSegment_060_2295_0016, g32p_row03_traceSegment_060_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2328 8 9, g32p_row03_traceSegment_060_2328_0008, g32p_row03_traceSegment_060_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2345 8 9, g32p_row03_traceSegment_060_2345_0008, g32p_row03_traceSegment_060_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2328 17 17, g32p_row03_traceSegment_060_2328_0017, g32p_row03_traceSegment_060_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 2295 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2295 33 34, g32p_row03_traceSegment_060_2295_0033, g32p_row03_traceSegment_060_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2362 8 9, g32p_row03_traceSegment_060_2362_0008, g32p_row03_traceSegment_060_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2379 8 9, g32p_row03_traceSegment_060_2379_0008, g32p_row03_traceSegment_060_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2362 17 17, g32p_row03_traceSegment_060_2362_0017, g32p_row03_traceSegment_060_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2396 8 9, g32p_row03_traceSegment_060_2396_0008, g32p_row03_traceSegment_060_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2413 8 9, g32p_row03_traceSegment_060_2413_0008, g32p_row03_traceSegment_060_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2396 17 17, g32p_row03_traceSegment_060_2396_0017, g32p_row03_traceSegment_060_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2362 34 34, g32p_row03_traceSegment_060_2362_0034, g32p_row03_traceSegment_060_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 2295 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2295 67 68, g32p_row03_traceSegment_060_2295_0067, g32p_row03_traceSegment_060_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 2160 270 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2160 135 135, g32p_row03_traceSegment_060_2160_0135, g32p_row03_traceSegment_060_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 2430 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2454 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2446 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2446 8 9, g32p_row03_traceSegment_060_2446_0008, g32p_row03_traceSegment_060_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 2430 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2430 16 17, g32p_row03_traceSegment_060_2430_0016, g32p_row03_traceSegment_060_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2463 8 9, g32p_row03_traceSegment_060_2463_0008, g32p_row03_traceSegment_060_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2480 8 9, g32p_row03_traceSegment_060_2480_0008, g32p_row03_traceSegment_060_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2463 17 17, g32p_row03_traceSegment_060_2463_0017, g32p_row03_traceSegment_060_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 2430 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2430 33 34, g32p_row03_traceSegment_060_2430_0033, g32p_row03_traceSegment_060_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2497 8 9, g32p_row03_traceSegment_060_2497_0008, g32p_row03_traceSegment_060_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2514 8 9, g32p_row03_traceSegment_060_2514_0008, g32p_row03_traceSegment_060_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2497 17 17, g32p_row03_traceSegment_060_2497_0017, g32p_row03_traceSegment_060_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2539 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2531 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2531 8 9, g32p_row03_traceSegment_060_2531_0008, g32p_row03_traceSegment_060_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2548 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2548 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2548 8 9, g32p_row03_traceSegment_060_2548_0008, g32p_row03_traceSegment_060_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2531 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2531 17 17, g32p_row03_traceSegment_060_2531_0017, g32p_row03_traceSegment_060_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 2497 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2497 34 34, g32p_row03_traceSegment_060_2497_0034, g32p_row03_traceSegment_060_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 2430 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2430 67 68, g32p_row03_traceSegment_060_2430_0067, g32p_row03_traceSegment_060_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2581 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2581 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2581 8 9, g32p_row03_traceSegment_060_2581_0008, g32p_row03_traceSegment_060_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 2565 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2565 16 17, g32p_row03_traceSegment_060_2565_0016, g32p_row03_traceSegment_060_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2598 8 9, g32p_row03_traceSegment_060_2598_0008, g32p_row03_traceSegment_060_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2623 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2615 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2615 8 9, g32p_row03_traceSegment_060_2615_0008, g32p_row03_traceSegment_060_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2598 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2598 17 17, g32p_row03_traceSegment_060_2598_0017, g32p_row03_traceSegment_060_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 2565 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2565 33 34, g32p_row03_traceSegment_060_2565_0033, g32p_row03_traceSegment_060_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2632 8 9, g32p_row03_traceSegment_060_2632_0008, g32p_row03_traceSegment_060_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2649 8 9, g32p_row03_traceSegment_060_2649_0008, g32p_row03_traceSegment_060_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2632 17 17, g32p_row03_traceSegment_060_2632_0017, g32p_row03_traceSegment_060_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2666 8 9, g32p_row03_traceSegment_060_2666_0008, g32p_row03_traceSegment_060_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2683 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2683 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2683 8 9, g32p_row03_traceSegment_060_2683_0008, g32p_row03_traceSegment_060_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2666 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2666 17 17, g32p_row03_traceSegment_060_2666_0017, g32p_row03_traceSegment_060_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 2632 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2632 34 34, g32p_row03_traceSegment_060_2632_0034, g32p_row03_traceSegment_060_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 2565 135 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2565 67 68, g32p_row03_traceSegment_060_2565_0067, g32p_row03_traceSegment_060_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 2430 270 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2430 135 135, g32p_row03_traceSegment_060_2430_0135, g32p_row03_traceSegment_060_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_060 2160 540 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2160 270 270, g32p_row03_traceSegment_060_2160_0270, g32p_row03_traceSegment_060_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2716 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2724 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2716 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2716 8 9, g32p_row03_traceSegment_060_2716_0008, g32p_row03_traceSegment_060_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 2700 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2700 16 17, g32p_row03_traceSegment_060_2700_0016, g32p_row03_traceSegment_060_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2733 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2733 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2733 8 9, g32p_row03_traceSegment_060_2733_0008, g32p_row03_traceSegment_060_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2750 8 9, g32p_row03_traceSegment_060_2750_0008, g32p_row03_traceSegment_060_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2733 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2733 17 17, g32p_row03_traceSegment_060_2733_0017, g32p_row03_traceSegment_060_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 2700 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2700 33 34, g32p_row03_traceSegment_060_2700_0033, g32p_row03_traceSegment_060_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2767 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2775 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2767 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2767 8 9, g32p_row03_traceSegment_060_2767_0008, g32p_row03_traceSegment_060_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2784 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2784 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2784 8 9, g32p_row03_traceSegment_060_2784_0008, g32p_row03_traceSegment_060_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2767 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2767 17 17, g32p_row03_traceSegment_060_2767_0017, g32p_row03_traceSegment_060_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2809 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2801 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2801 8 9, g32p_row03_traceSegment_060_2801_0008, g32p_row03_traceSegment_060_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2818 8 9, g32p_row03_traceSegment_060_2818_0008, g32p_row03_traceSegment_060_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2801 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2801 17 17, g32p_row03_traceSegment_060_2801_0017, g32p_row03_traceSegment_060_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 2767 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2767 34 34, g32p_row03_traceSegment_060_2767_0034, g32p_row03_traceSegment_060_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 2700 135 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2700 67 68, g32p_row03_traceSegment_060_2700_0067, g32p_row03_traceSegment_060_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2851 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2851 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2851 8 9, g32p_row03_traceSegment_060_2851_0008, g32p_row03_traceSegment_060_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 2835 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2835 16 17, g32p_row03_traceSegment_060_2835_0016, g32p_row03_traceSegment_060_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2876 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2868 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2868 8 9, g32p_row03_traceSegment_060_2868_0008, g32p_row03_traceSegment_060_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2885 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2893 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2885 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2885 8 9, g32p_row03_traceSegment_060_2885_0008, g32p_row03_traceSegment_060_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2868 34 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2868 17 17, g32p_row03_traceSegment_060_2868_0017, g32p_row03_traceSegment_060_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 2835 67 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2835 33 34, g32p_row03_traceSegment_060_2835_0033, g32p_row03_traceSegment_060_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2910 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2902 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2902 8 9, g32p_row03_traceSegment_060_2902_0008, g32p_row03_traceSegment_060_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2927 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2919 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2919 8 9, g32p_row03_traceSegment_060_2919_0008, g32p_row03_traceSegment_060_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2902 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2902 17 17, g32p_row03_traceSegment_060_2902_0017, g32p_row03_traceSegment_060_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2936 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2936 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2936 8 9, g32p_row03_traceSegment_060_2936_0008, g32p_row03_traceSegment_060_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2953 8 9, g32p_row03_traceSegment_060_2953_0008, g32p_row03_traceSegment_060_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 2936 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2936 17 17, g32p_row03_traceSegment_060_2936_0017, g32p_row03_traceSegment_060_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 2902 68 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2902 34 34, g32p_row03_traceSegment_060_2902_0034, g32p_row03_traceSegment_060_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 2835 135 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2835 67 68, g32p_row03_traceSegment_060_2835_0067, g32p_row03_traceSegment_060_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 2700 270 = [0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2700 135 135, g32p_row03_traceSegment_060_2700_0135, g32p_row03_traceSegment_060_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 2970 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 2994 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 2986 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2986 8 9, g32p_row03_traceSegment_060_2986_0008, g32p_row03_traceSegment_060_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 2970 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2970 16 17, g32p_row03_traceSegment_060_2970_0016, g32p_row03_traceSegment_060_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3003 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3011 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3003 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3003 8 9, g32p_row03_traceSegment_060_3003_0008, g32p_row03_traceSegment_060_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3028 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3020 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3020 8 9, g32p_row03_traceSegment_060_3020_0008, g32p_row03_traceSegment_060_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3003 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3003 17 17, g32p_row03_traceSegment_060_3003_0017, g32p_row03_traceSegment_060_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 2970 67 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2970 33 34, g32p_row03_traceSegment_060_2970_0033, g32p_row03_traceSegment_060_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3045 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3037 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3037 8 9, g32p_row03_traceSegment_060_3037_0008, g32p_row03_traceSegment_060_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3054 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3054 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3054 8 9, g32p_row03_traceSegment_060_3054_0008, g32p_row03_traceSegment_060_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3037 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3037 17 17, g32p_row03_traceSegment_060_3037_0017, g32p_row03_traceSegment_060_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3071 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3071 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3071 8 9, g32p_row03_traceSegment_060_3071_0008, g32p_row03_traceSegment_060_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3088 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3096 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3088 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3088 8 9, g32p_row03_traceSegment_060_3088_0008, g32p_row03_traceSegment_060_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3071 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3071 17 17, g32p_row03_traceSegment_060_3071_0017, g32p_row03_traceSegment_060_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 3037 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3037 34 34, g32p_row03_traceSegment_060_3037_0034, g32p_row03_traceSegment_060_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 2970 135 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2970 67 68, g32p_row03_traceSegment_060_2970_0067, g32p_row03_traceSegment_060_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 3105 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3121 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3121 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3121 8 9, g32p_row03_traceSegment_060_3121_0008, g32p_row03_traceSegment_060_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 3105 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3105 16 17, g32p_row03_traceSegment_060_3105_0016, g32p_row03_traceSegment_060_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3138 8 9, g32p_row03_traceSegment_060_3138_0008, g32p_row03_traceSegment_060_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3155 8 9, g32p_row03_traceSegment_060_3155_0008, g32p_row03_traceSegment_060_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3138 17 17, g32p_row03_traceSegment_060_3138_0017, g32p_row03_traceSegment_060_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 3105 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3105 33 34, g32p_row03_traceSegment_060_3105_0033, g32p_row03_traceSegment_060_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3172 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3172 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3172 8 9, g32p_row03_traceSegment_060_3172_0008, g32p_row03_traceSegment_060_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3197 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3189 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3189 8 9, g32p_row03_traceSegment_060_3189_0008, g32p_row03_traceSegment_060_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3172 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3172 17 17, g32p_row03_traceSegment_060_3172_0017, g32p_row03_traceSegment_060_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3206 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3214 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3206 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3206 8 9, g32p_row03_traceSegment_060_3206_0008, g32p_row03_traceSegment_060_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3223 8 9, g32p_row03_traceSegment_060_3223_0008, g32p_row03_traceSegment_060_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3206 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3206 17 17, g32p_row03_traceSegment_060_3206_0017, g32p_row03_traceSegment_060_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 3172 68 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3172 34 34, g32p_row03_traceSegment_060_3172_0034, g32p_row03_traceSegment_060_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 3105 135 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3105 67 68, g32p_row03_traceSegment_060_3105_0067, g32p_row03_traceSegment_060_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 2970 270 = [0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2970 135 135, g32p_row03_traceSegment_060_2970_0135, g32p_row03_traceSegment_060_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_060 2700 540 = [0, 0, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2700 270 270, g32p_row03_traceSegment_060_2700_0270, g32p_row03_traceSegment_060_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_060 2160 1080 = [0, 0, 0, 0, 46] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2160 540 540, g32p_row03_traceSegment_060_2160_0540, g32p_row03_traceSegment_060_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3256 8 9, g32p_row03_traceSegment_060_3256_0008, g32p_row03_traceSegment_060_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3240 16 17, g32p_row03_traceSegment_060_3240_0016, g32p_row03_traceSegment_060_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3273 8 9, g32p_row03_traceSegment_060_3273_0008, g32p_row03_traceSegment_060_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3290 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3290 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3290 8 9, g32p_row03_traceSegment_060_3290_0008, g32p_row03_traceSegment_060_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3273 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3273 17 17, g32p_row03_traceSegment_060_3273_0017, g32p_row03_traceSegment_060_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 3240 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3240 33 34, g32p_row03_traceSegment_060_3240_0033, g32p_row03_traceSegment_060_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3307 8 9, g32p_row03_traceSegment_060_3307_0008, g32p_row03_traceSegment_060_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3324 8 9, g32p_row03_traceSegment_060_3324_0008, g32p_row03_traceSegment_060_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3307 17 17, g32p_row03_traceSegment_060_3307_0017, g32p_row03_traceSegment_060_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3341 8 9, g32p_row03_traceSegment_060_3341_0008, g32p_row03_traceSegment_060_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3366 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3358 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3358 8 9, g32p_row03_traceSegment_060_3358_0008, g32p_row03_traceSegment_060_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3341 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3341 17 17, g32p_row03_traceSegment_060_3341_0017, g32p_row03_traceSegment_060_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 3307 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3307 34 34, g32p_row03_traceSegment_060_3307_0034, g32p_row03_traceSegment_060_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 3240 135 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3240 67 68, g32p_row03_traceSegment_060_3240_0067, g32p_row03_traceSegment_060_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 3375 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3399 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3391 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3391 8 9, g32p_row03_traceSegment_060_3391_0008, g32p_row03_traceSegment_060_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 3375 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3375 16 17, g32p_row03_traceSegment_060_3375_0016, g32p_row03_traceSegment_060_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3416 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3408 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3408 8 9, g32p_row03_traceSegment_060_3408_0008, g32p_row03_traceSegment_060_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3425 8 9, g32p_row03_traceSegment_060_3425_0008, g32p_row03_traceSegment_060_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3408 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3408 17 17, g32p_row03_traceSegment_060_3408_0017, g32p_row03_traceSegment_060_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 3375 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3375 33 34, g32p_row03_traceSegment_060_3375_0033, g32p_row03_traceSegment_060_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3442 8 9, g32p_row03_traceSegment_060_3442_0008, g32p_row03_traceSegment_060_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3459 8 9, g32p_row03_traceSegment_060_3459_0008, g32p_row03_traceSegment_060_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3442 17 17, g32p_row03_traceSegment_060_3442_0017, g32p_row03_traceSegment_060_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3484 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3476 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3476 8 9, g32p_row03_traceSegment_060_3476_0008, g32p_row03_traceSegment_060_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3493 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3493 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3493 8 9, g32p_row03_traceSegment_060_3493_0008, g32p_row03_traceSegment_060_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3476 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3476 17 17, g32p_row03_traceSegment_060_3476_0017, g32p_row03_traceSegment_060_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 3442 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3442 34 34, g32p_row03_traceSegment_060_3442_0034, g32p_row03_traceSegment_060_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 3375 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3375 67 68, g32p_row03_traceSegment_060_3375_0067, g32p_row03_traceSegment_060_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 3240 270 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3240 135 135, g32p_row03_traceSegment_060_3240_0135, g32p_row03_traceSegment_060_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3526 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3526 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3526 8 9, g32p_row03_traceSegment_060_3526_0008, g32p_row03_traceSegment_060_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 3510 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3510 16 17, g32p_row03_traceSegment_060_3510_0016, g32p_row03_traceSegment_060_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3543 8 9, g32p_row03_traceSegment_060_3543_0008, g32p_row03_traceSegment_060_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3568 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3560 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3560 8 9, g32p_row03_traceSegment_060_3560_0008, g32p_row03_traceSegment_060_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3543 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3543 17 17, g32p_row03_traceSegment_060_3543_0017, g32p_row03_traceSegment_060_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 3510 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3510 33 34, g32p_row03_traceSegment_060_3510_0033, g32p_row03_traceSegment_060_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3577 8 9, g32p_row03_traceSegment_060_3577_0008, g32p_row03_traceSegment_060_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3594 8 9, g32p_row03_traceSegment_060_3594_0008, g32p_row03_traceSegment_060_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3577 17 17, g32p_row03_traceSegment_060_3577_0017, g32p_row03_traceSegment_060_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3611 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3611 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3611 8 9, g32p_row03_traceSegment_060_3611_0008, g32p_row03_traceSegment_060_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3636 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3628 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3628 8 9, g32p_row03_traceSegment_060_3628_0008, g32p_row03_traceSegment_060_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3611 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3611 17 17, g32p_row03_traceSegment_060_3611_0017, g32p_row03_traceSegment_060_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 3577 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3577 34 34, g32p_row03_traceSegment_060_3577_0034, g32p_row03_traceSegment_060_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 3510 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3510 67 68, g32p_row03_traceSegment_060_3510_0067, g32p_row03_traceSegment_060_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 3645 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3669 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3661 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3661 8 9, g32p_row03_traceSegment_060_3661_0008, g32p_row03_traceSegment_060_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 3645 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3645 16 17, g32p_row03_traceSegment_060_3645_0016, g32p_row03_traceSegment_060_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3678 8 9, g32p_row03_traceSegment_060_3678_0008, g32p_row03_traceSegment_060_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3695 8 9, g32p_row03_traceSegment_060_3695_0008, g32p_row03_traceSegment_060_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3678 17 17, g32p_row03_traceSegment_060_3678_0017, g32p_row03_traceSegment_060_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 3645 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3645 33 34, g32p_row03_traceSegment_060_3645_0033, g32p_row03_traceSegment_060_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3712 8 9, g32p_row03_traceSegment_060_3712_0008, g32p_row03_traceSegment_060_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3729 8 9, g32p_row03_traceSegment_060_3729_0008, g32p_row03_traceSegment_060_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3712 17 17, g32p_row03_traceSegment_060_3712_0017, g32p_row03_traceSegment_060_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3746 8 9, g32p_row03_traceSegment_060_3746_0008, g32p_row03_traceSegment_060_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3763 8 9, g32p_row03_traceSegment_060_3763_0008, g32p_row03_traceSegment_060_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3746 17 17, g32p_row03_traceSegment_060_3746_0017, g32p_row03_traceSegment_060_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3712 34 34, g32p_row03_traceSegment_060_3712_0034, g32p_row03_traceSegment_060_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 3645 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3645 67 68, g32p_row03_traceSegment_060_3645_0067, g32p_row03_traceSegment_060_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 3510 270 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3510 135 135, g32p_row03_traceSegment_060_3510_0135, g32p_row03_traceSegment_060_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_060 3240 540 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3240 270 270, g32p_row03_traceSegment_060_3240_0270, g32p_row03_traceSegment_060_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3796 8 9, g32p_row03_traceSegment_060_3796_0008, g32p_row03_traceSegment_060_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3780 16 17, g32p_row03_traceSegment_060_3780_0016, g32p_row03_traceSegment_060_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3813 8 9, g32p_row03_traceSegment_060_3813_0008, g32p_row03_traceSegment_060_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3830 8 9, g32p_row03_traceSegment_060_3830_0008, g32p_row03_traceSegment_060_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3813 17 17, g32p_row03_traceSegment_060_3813_0017, g32p_row03_traceSegment_060_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3780 33 34, g32p_row03_traceSegment_060_3780_0033, g32p_row03_traceSegment_060_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3847 8 9, g32p_row03_traceSegment_060_3847_0008, g32p_row03_traceSegment_060_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3864 8 9, g32p_row03_traceSegment_060_3864_0008, g32p_row03_traceSegment_060_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3847 17 17, g32p_row03_traceSegment_060_3847_0017, g32p_row03_traceSegment_060_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3881 8 9, g32p_row03_traceSegment_060_3881_0008, g32p_row03_traceSegment_060_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3906 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3898 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3898 8 9, g32p_row03_traceSegment_060_3898_0008, g32p_row03_traceSegment_060_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3881 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3881 17 17, g32p_row03_traceSegment_060_3881_0017, g32p_row03_traceSegment_060_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 3847 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3847 34 34, g32p_row03_traceSegment_060_3847_0034, g32p_row03_traceSegment_060_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 3780 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3780 67 68, g32p_row03_traceSegment_060_3780_0067, g32p_row03_traceSegment_060_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 3915 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3931 8 9, g32p_row03_traceSegment_060_3931_0008, g32p_row03_traceSegment_060_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 3915 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3915 16 17, g32p_row03_traceSegment_060_3915_0016, g32p_row03_traceSegment_060_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3956 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3948 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3948 8 9, g32p_row03_traceSegment_060_3948_0008, g32p_row03_traceSegment_060_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3965 8 9, g32p_row03_traceSegment_060_3965_0008, g32p_row03_traceSegment_060_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3948 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3948 17 17, g32p_row03_traceSegment_060_3948_0017, g32p_row03_traceSegment_060_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 3915 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3915 33 34, g32p_row03_traceSegment_060_3915_0033, g32p_row03_traceSegment_060_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3982 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 3990 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3982 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3982 8 9, g32p_row03_traceSegment_060_3982_0008, g32p_row03_traceSegment_060_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 3999 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 3999 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3999 8 9, g32p_row03_traceSegment_060_3999_0008, g32p_row03_traceSegment_060_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 3982 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3982 17 17, g32p_row03_traceSegment_060_3982_0017, g32p_row03_traceSegment_060_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4016 8 9, g32p_row03_traceSegment_060_4016_0008, g32p_row03_traceSegment_060_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4041 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4033 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4033 8 9, g32p_row03_traceSegment_060_4033_0008, g32p_row03_traceSegment_060_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 4016 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4016 17 17, g32p_row03_traceSegment_060_4016_0017, g32p_row03_traceSegment_060_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 3982 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3982 34 34, g32p_row03_traceSegment_060_3982_0034, g32p_row03_traceSegment_060_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 3915 135 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3915 67 68, g32p_row03_traceSegment_060_3915_0067, g32p_row03_traceSegment_060_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 3780 270 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3780 135 135, g32p_row03_traceSegment_060_3780_0135, g32p_row03_traceSegment_060_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 4050 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4066 8 9, g32p_row03_traceSegment_060_4066_0008, g32p_row03_traceSegment_060_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 4050 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4050 16 17, g32p_row03_traceSegment_060_4050_0016, g32p_row03_traceSegment_060_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4083 8 9, g32p_row03_traceSegment_060_4083_0008, g32p_row03_traceSegment_060_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4100 8 9, g32p_row03_traceSegment_060_4100_0008, g32p_row03_traceSegment_060_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4083 17 17, g32p_row03_traceSegment_060_4083_0017, g32p_row03_traceSegment_060_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 4050 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4050 33 34, g32p_row03_traceSegment_060_4050_0033, g32p_row03_traceSegment_060_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4117 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4125 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4117 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4117 8 9, g32p_row03_traceSegment_060_4117_0008, g32p_row03_traceSegment_060_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4134 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4134 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4134 8 9, g32p_row03_traceSegment_060_4134_0008, g32p_row03_traceSegment_060_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 4117 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4117 17 17, g32p_row03_traceSegment_060_4117_0017, g32p_row03_traceSegment_060_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4151 8 9, g32p_row03_traceSegment_060_4151_0008, g32p_row03_traceSegment_060_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4176 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4168 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4168 8 9, g32p_row03_traceSegment_060_4168_0008, g32p_row03_traceSegment_060_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 4151 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4151 17 17, g32p_row03_traceSegment_060_4151_0017, g32p_row03_traceSegment_060_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 4117 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4117 34 34, g32p_row03_traceSegment_060_4117_0034, g32p_row03_traceSegment_060_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 4050 135 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4050 67 68, g32p_row03_traceSegment_060_4050_0067, g32p_row03_traceSegment_060_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_060 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4201 8 9, g32p_row03_traceSegment_060_4201_0008, g32p_row03_traceSegment_060_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_060 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4185 16 17, g32p_row03_traceSegment_060_4185_0016, g32p_row03_traceSegment_060_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4218 8 9, g32p_row03_traceSegment_060_4218_0008, g32p_row03_traceSegment_060_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4235 8 9, g32p_row03_traceSegment_060_4235_0008, g32p_row03_traceSegment_060_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4218 17 17, g32p_row03_traceSegment_060_4218_0017, g32p_row03_traceSegment_060_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_060 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4185 33 34, g32p_row03_traceSegment_060_4185_0033, g32p_row03_traceSegment_060_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4252 8 9, g32p_row03_traceSegment_060_4252_0008, g32p_row03_traceSegment_060_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4277 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4269 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4269 8 9, g32p_row03_traceSegment_060_4269_0008, g32p_row03_traceSegment_060_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 4252 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4252 17 17, g32p_row03_traceSegment_060_4252_0017, g32p_row03_traceSegment_060_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4286 8 9, g32p_row03_traceSegment_060_4286_0008, g32p_row03_traceSegment_060_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_060 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_060 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_060_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_060 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4303 8 9, g32p_row03_traceSegment_060_4303_0008, g32p_row03_traceSegment_060_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_060 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4286 17 17, g32p_row03_traceSegment_060_4286_0017, g32p_row03_traceSegment_060_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_060 4252 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4252 34 34, g32p_row03_traceSegment_060_4252_0034, g32p_row03_traceSegment_060_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_060 4185 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4185 67 68, g32p_row03_traceSegment_060_4185_0067, g32p_row03_traceSegment_060_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_060_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_060 4050 270 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 4050 135 135, g32p_row03_traceSegment_060_4050_0135, g32p_row03_traceSegment_060_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_060 3780 540 = [0, 0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3780 270 270, g32p_row03_traceSegment_060_3780_0270, g32p_row03_traceSegment_060_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_060_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_060 3240 1080 = [0, 0, 0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 3240 540 540, g32p_row03_traceSegment_060_3240_0540, g32p_row03_traceSegment_060_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_060_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_060 2160 2160 = [0, 0, 0, 0, 77] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 2160 1080 1080, g32p_row03_traceSegment_060_2160_1080, g32p_row03_traceSegment_060_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_060_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_060 0 4320 = [0, 0, 0, 0, 144] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_060 0 2160 2160, g32p_row03_traceSegment_060_0000_2160, g32p_row03_traceSegment_060_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_060 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 60 = [0, 0, 0, 0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_060_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_065 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 65 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_065_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 16 8 9, g32p_row03_traceSegment_065_0016_0008, g32p_row03_traceSegment_065_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 0 16 17, g32p_row03_traceSegment_065_0000_0016, g32p_row03_traceSegment_065_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 33 8 9, g32p_row03_traceSegment_065_0033_0008, g32p_row03_traceSegment_065_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 50 8 9, g32p_row03_traceSegment_065_0050_0008, g32p_row03_traceSegment_065_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 33 17 17, g32p_row03_traceSegment_065_0033_0017, g32p_row03_traceSegment_065_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 0 33 34, g32p_row03_traceSegment_065_0000_0033, g32p_row03_traceSegment_065_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 67 8 9, g32p_row03_traceSegment_065_0067_0008, g32p_row03_traceSegment_065_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 84 8 9, g32p_row03_traceSegment_065_0084_0008, g32p_row03_traceSegment_065_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 67 17 17, g32p_row03_traceSegment_065_0067_0017, g32p_row03_traceSegment_065_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 101 8 9, g32p_row03_traceSegment_065_0101_0008, g32p_row03_traceSegment_065_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 118 8 9, g32p_row03_traceSegment_065_0118_0008, g32p_row03_traceSegment_065_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 101 17 17, g32p_row03_traceSegment_065_0101_0017, g32p_row03_traceSegment_065_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 67 34 34, g32p_row03_traceSegment_065_0067_0034, g32p_row03_traceSegment_065_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 0 67 68, g32p_row03_traceSegment_065_0000_0067, g32p_row03_traceSegment_065_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 151 8 9, g32p_row03_traceSegment_065_0151_0008, g32p_row03_traceSegment_065_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 135 16 17, g32p_row03_traceSegment_065_0135_0016, g32p_row03_traceSegment_065_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 168 8 9, g32p_row03_traceSegment_065_0168_0008, g32p_row03_traceSegment_065_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 185 8 9, g32p_row03_traceSegment_065_0185_0008, g32p_row03_traceSegment_065_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 168 17 17, g32p_row03_traceSegment_065_0168_0017, g32p_row03_traceSegment_065_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 135 33 34, g32p_row03_traceSegment_065_0135_0033, g32p_row03_traceSegment_065_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 202 8 9, g32p_row03_traceSegment_065_0202_0008, g32p_row03_traceSegment_065_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 219 8 9, g32p_row03_traceSegment_065_0219_0008, g32p_row03_traceSegment_065_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 202 17 17, g32p_row03_traceSegment_065_0202_0017, g32p_row03_traceSegment_065_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 236 8 9, g32p_row03_traceSegment_065_0236_0008, g32p_row03_traceSegment_065_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 253 8 9, g32p_row03_traceSegment_065_0253_0008, g32p_row03_traceSegment_065_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 236 17 17, g32p_row03_traceSegment_065_0236_0017, g32p_row03_traceSegment_065_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 202 34 34, g32p_row03_traceSegment_065_0202_0034, g32p_row03_traceSegment_065_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 135 67 68, g32p_row03_traceSegment_065_0135_0067, g32p_row03_traceSegment_065_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 0 135 135, g32p_row03_traceSegment_065_0000_0135, g32p_row03_traceSegment_065_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 286 8 9, g32p_row03_traceSegment_065_0286_0008, g32p_row03_traceSegment_065_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 270 16 17, g32p_row03_traceSegment_065_0270_0016, g32p_row03_traceSegment_065_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 303 8 9, g32p_row03_traceSegment_065_0303_0008, g32p_row03_traceSegment_065_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 320 8 9, g32p_row03_traceSegment_065_0320_0008, g32p_row03_traceSegment_065_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 303 17 17, g32p_row03_traceSegment_065_0303_0017, g32p_row03_traceSegment_065_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 270 33 34, g32p_row03_traceSegment_065_0270_0033, g32p_row03_traceSegment_065_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 337 8 9, g32p_row03_traceSegment_065_0337_0008, g32p_row03_traceSegment_065_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 354 8 9, g32p_row03_traceSegment_065_0354_0008, g32p_row03_traceSegment_065_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 337 17 17, g32p_row03_traceSegment_065_0337_0017, g32p_row03_traceSegment_065_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 371 8 9, g32p_row03_traceSegment_065_0371_0008, g32p_row03_traceSegment_065_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 388 8 9, g32p_row03_traceSegment_065_0388_0008, g32p_row03_traceSegment_065_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 371 17 17, g32p_row03_traceSegment_065_0371_0017, g32p_row03_traceSegment_065_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 337 34 34, g32p_row03_traceSegment_065_0337_0034, g32p_row03_traceSegment_065_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 270 67 68, g32p_row03_traceSegment_065_0270_0067, g32p_row03_traceSegment_065_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 421 8 9, g32p_row03_traceSegment_065_0421_0008, g32p_row03_traceSegment_065_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 405 16 17, g32p_row03_traceSegment_065_0405_0016, g32p_row03_traceSegment_065_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 438 8 9, g32p_row03_traceSegment_065_0438_0008, g32p_row03_traceSegment_065_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 455 8 9, g32p_row03_traceSegment_065_0455_0008, g32p_row03_traceSegment_065_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 438 17 17, g32p_row03_traceSegment_065_0438_0017, g32p_row03_traceSegment_065_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 405 33 34, g32p_row03_traceSegment_065_0405_0033, g32p_row03_traceSegment_065_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 472 8 9, g32p_row03_traceSegment_065_0472_0008, g32p_row03_traceSegment_065_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 489 8 9, g32p_row03_traceSegment_065_0489_0008, g32p_row03_traceSegment_065_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 472 17 17, g32p_row03_traceSegment_065_0472_0017, g32p_row03_traceSegment_065_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 506 8 9, g32p_row03_traceSegment_065_0506_0008, g32p_row03_traceSegment_065_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 523 8 9, g32p_row03_traceSegment_065_0523_0008, g32p_row03_traceSegment_065_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 506 17 17, g32p_row03_traceSegment_065_0506_0017, g32p_row03_traceSegment_065_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 472 34 34, g32p_row03_traceSegment_065_0472_0034, g32p_row03_traceSegment_065_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 405 67 68, g32p_row03_traceSegment_065_0405_0067, g32p_row03_traceSegment_065_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 270 135 135, g32p_row03_traceSegment_065_0270_0135, g32p_row03_traceSegment_065_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_065 0 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 0 270 270, g32p_row03_traceSegment_065_0000_0270, g32p_row03_traceSegment_065_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 556 8 9, g32p_row03_traceSegment_065_0556_0008, g32p_row03_traceSegment_065_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 540 16 17, g32p_row03_traceSegment_065_0540_0016, g32p_row03_traceSegment_065_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 573 8 9, g32p_row03_traceSegment_065_0573_0008, g32p_row03_traceSegment_065_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 590 8 9, g32p_row03_traceSegment_065_0590_0008, g32p_row03_traceSegment_065_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 573 17 17, g32p_row03_traceSegment_065_0573_0017, g32p_row03_traceSegment_065_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 540 33 34, g32p_row03_traceSegment_065_0540_0033, g32p_row03_traceSegment_065_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 607 8 9, g32p_row03_traceSegment_065_0607_0008, g32p_row03_traceSegment_065_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 624 8 9, g32p_row03_traceSegment_065_0624_0008, g32p_row03_traceSegment_065_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 607 17 17, g32p_row03_traceSegment_065_0607_0017, g32p_row03_traceSegment_065_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 641 8 9, g32p_row03_traceSegment_065_0641_0008, g32p_row03_traceSegment_065_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 658 8 9, g32p_row03_traceSegment_065_0658_0008, g32p_row03_traceSegment_065_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 641 17 17, g32p_row03_traceSegment_065_0641_0017, g32p_row03_traceSegment_065_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 607 34 34, g32p_row03_traceSegment_065_0607_0034, g32p_row03_traceSegment_065_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 540 67 68, g32p_row03_traceSegment_065_0540_0067, g32p_row03_traceSegment_065_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 691 8 9, g32p_row03_traceSegment_065_0691_0008, g32p_row03_traceSegment_065_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 675 16 17, g32p_row03_traceSegment_065_0675_0016, g32p_row03_traceSegment_065_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 708 8 9, g32p_row03_traceSegment_065_0708_0008, g32p_row03_traceSegment_065_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 725 8 9, g32p_row03_traceSegment_065_0725_0008, g32p_row03_traceSegment_065_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 708 17 17, g32p_row03_traceSegment_065_0708_0017, g32p_row03_traceSegment_065_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 675 33 34, g32p_row03_traceSegment_065_0675_0033, g32p_row03_traceSegment_065_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 742 8 9, g32p_row03_traceSegment_065_0742_0008, g32p_row03_traceSegment_065_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 759 8 9, g32p_row03_traceSegment_065_0759_0008, g32p_row03_traceSegment_065_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 742 17 17, g32p_row03_traceSegment_065_0742_0017, g32p_row03_traceSegment_065_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 776 8 9, g32p_row03_traceSegment_065_0776_0008, g32p_row03_traceSegment_065_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 793 8 9, g32p_row03_traceSegment_065_0793_0008, g32p_row03_traceSegment_065_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 776 17 17, g32p_row03_traceSegment_065_0776_0017, g32p_row03_traceSegment_065_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 742 34 34, g32p_row03_traceSegment_065_0742_0034, g32p_row03_traceSegment_065_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 675 67 68, g32p_row03_traceSegment_065_0675_0067, g32p_row03_traceSegment_065_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 540 135 135, g32p_row03_traceSegment_065_0540_0135, g32p_row03_traceSegment_065_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 810 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 826 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 826 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 826 8 9, g32p_row03_traceSegment_065_0826_0008, g32p_row03_traceSegment_065_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 810 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 810 16 17, g32p_row03_traceSegment_065_0810_0016, g32p_row03_traceSegment_065_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 843 8 9, g32p_row03_traceSegment_065_0843_0008, g32p_row03_traceSegment_065_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 860 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 868 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 860 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 860 8 9, g32p_row03_traceSegment_065_0860_0008, g32p_row03_traceSegment_065_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 843 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 843 17 17, g32p_row03_traceSegment_065_0843_0017, g32p_row03_traceSegment_065_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 810 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 810 33 34, g32p_row03_traceSegment_065_0810_0033, g32p_row03_traceSegment_065_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 877 8 9, g32p_row03_traceSegment_065_0877_0008, g32p_row03_traceSegment_065_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 902 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 894 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 894 8 9, g32p_row03_traceSegment_065_0894_0008, g32p_row03_traceSegment_065_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 877 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 877 17 17, g32p_row03_traceSegment_065_0877_0017, g32p_row03_traceSegment_065_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 911 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 919 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 911 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 911 8 9, g32p_row03_traceSegment_065_0911_0008, g32p_row03_traceSegment_065_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 928 8 9, g32p_row03_traceSegment_065_0928_0008, g32p_row03_traceSegment_065_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 911 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 911 17 17, g32p_row03_traceSegment_065_0911_0017, g32p_row03_traceSegment_065_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 877 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 877 34 34, g32p_row03_traceSegment_065_0877_0034, g32p_row03_traceSegment_065_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 810 135 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 810 67 68, g32p_row03_traceSegment_065_0810_0067, g32p_row03_traceSegment_065_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 961 8 9, g32p_row03_traceSegment_065_0961_0008, g32p_row03_traceSegment_065_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 945 16 17, g32p_row03_traceSegment_065_0945_0016, g32p_row03_traceSegment_065_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 978 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 978 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 978 8 9, g32p_row03_traceSegment_065_0978_0008, g32p_row03_traceSegment_065_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 995 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 995 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 995 8 9, g32p_row03_traceSegment_065_0995_0008, g32p_row03_traceSegment_065_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 978 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 978 17 17, g32p_row03_traceSegment_065_0978_0017, g32p_row03_traceSegment_065_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 945 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 945 33 34, g32p_row03_traceSegment_065_0945_0033, g32p_row03_traceSegment_065_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1012 8 9, g32p_row03_traceSegment_065_1012_0008, g32p_row03_traceSegment_065_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1029 8 9, g32p_row03_traceSegment_065_1029_0008, g32p_row03_traceSegment_065_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1012 17 17, g32p_row03_traceSegment_065_1012_0017, g32p_row03_traceSegment_065_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1054 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1046 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1046 8 9, g32p_row03_traceSegment_065_1046_0008, g32p_row03_traceSegment_065_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1063 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1063 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1063 8 9, g32p_row03_traceSegment_065_1063_0008, g32p_row03_traceSegment_065_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1046 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1046 17 17, g32p_row03_traceSegment_065_1046_0017, g32p_row03_traceSegment_065_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 1012 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1012 34 34, g32p_row03_traceSegment_065_1012_0034, g32p_row03_traceSegment_065_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 945 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 945 67 68, g32p_row03_traceSegment_065_0945_0067, g32p_row03_traceSegment_065_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 810 270 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 810 135 135, g32p_row03_traceSegment_065_0810_0135, g32p_row03_traceSegment_065_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_065 540 540 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 540 270 270, g32p_row03_traceSegment_065_0540_0270, g32p_row03_traceSegment_065_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_065 0 1080 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 0 540 540, g32p_row03_traceSegment_065_0000_0540, g32p_row03_traceSegment_065_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 1080 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1096 8 9, g32p_row03_traceSegment_065_1096_0008, g32p_row03_traceSegment_065_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 1080 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1080 16 17, g32p_row03_traceSegment_065_1080_0016, g32p_row03_traceSegment_065_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1113 8 9, g32p_row03_traceSegment_065_1113_0008, g32p_row03_traceSegment_065_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1130 8 9, g32p_row03_traceSegment_065_1130_0008, g32p_row03_traceSegment_065_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1113 17 17, g32p_row03_traceSegment_065_1113_0017, g32p_row03_traceSegment_065_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 1080 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1080 33 34, g32p_row03_traceSegment_065_1080_0033, g32p_row03_traceSegment_065_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1147 8 9, g32p_row03_traceSegment_065_1147_0008, g32p_row03_traceSegment_065_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1164 8 9, g32p_row03_traceSegment_065_1164_0008, g32p_row03_traceSegment_065_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1147 17 17, g32p_row03_traceSegment_065_1147_0017, g32p_row03_traceSegment_065_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1189 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1181 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1181 8 9, g32p_row03_traceSegment_065_1181_0008, g32p_row03_traceSegment_065_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1206 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1198 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1198 8 9, g32p_row03_traceSegment_065_1198_0008, g32p_row03_traceSegment_065_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1181 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1181 17 17, g32p_row03_traceSegment_065_1181_0017, g32p_row03_traceSegment_065_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 1147 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1147 34 34, g32p_row03_traceSegment_065_1147_0034, g32p_row03_traceSegment_065_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 1080 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1080 67 68, g32p_row03_traceSegment_065_1080_0067, g32p_row03_traceSegment_065_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1231 8 9, g32p_row03_traceSegment_065_1231_0008, g32p_row03_traceSegment_065_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1215 16 17, g32p_row03_traceSegment_065_1215_0016, g32p_row03_traceSegment_065_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1248 8 9, g32p_row03_traceSegment_065_1248_0008, g32p_row03_traceSegment_065_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1265 8 9, g32p_row03_traceSegment_065_1265_0008, g32p_row03_traceSegment_065_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1248 17 17, g32p_row03_traceSegment_065_1248_0017, g32p_row03_traceSegment_065_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1215 33 34, g32p_row03_traceSegment_065_1215_0033, g32p_row03_traceSegment_065_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1282 8 9, g32p_row03_traceSegment_065_1282_0008, g32p_row03_traceSegment_065_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1299 8 9, g32p_row03_traceSegment_065_1299_0008, g32p_row03_traceSegment_065_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1282 17 17, g32p_row03_traceSegment_065_1282_0017, g32p_row03_traceSegment_065_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1316 8 9, g32p_row03_traceSegment_065_1316_0008, g32p_row03_traceSegment_065_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1333 8 9, g32p_row03_traceSegment_065_1333_0008, g32p_row03_traceSegment_065_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1316 17 17, g32p_row03_traceSegment_065_1316_0017, g32p_row03_traceSegment_065_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1282 34 34, g32p_row03_traceSegment_065_1282_0034, g32p_row03_traceSegment_065_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1215 67 68, g32p_row03_traceSegment_065_1215_0067, g32p_row03_traceSegment_065_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 1080 270 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1080 135 135, g32p_row03_traceSegment_065_1080_0135, g32p_row03_traceSegment_065_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1366 8 9, g32p_row03_traceSegment_065_1366_0008, g32p_row03_traceSegment_065_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1350 16 17, g32p_row03_traceSegment_065_1350_0016, g32p_row03_traceSegment_065_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1383 8 9, g32p_row03_traceSegment_065_1383_0008, g32p_row03_traceSegment_065_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1400 8 9, g32p_row03_traceSegment_065_1400_0008, g32p_row03_traceSegment_065_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1383 17 17, g32p_row03_traceSegment_065_1383_0017, g32p_row03_traceSegment_065_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1350 33 34, g32p_row03_traceSegment_065_1350_0033, g32p_row03_traceSegment_065_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1417 8 9, g32p_row03_traceSegment_065_1417_0008, g32p_row03_traceSegment_065_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1434 8 9, g32p_row03_traceSegment_065_1434_0008, g32p_row03_traceSegment_065_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1417 17 17, g32p_row03_traceSegment_065_1417_0017, g32p_row03_traceSegment_065_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1451 8 9, g32p_row03_traceSegment_065_1451_0008, g32p_row03_traceSegment_065_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1468 8 9, g32p_row03_traceSegment_065_1468_0008, g32p_row03_traceSegment_065_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1451 17 17, g32p_row03_traceSegment_065_1451_0017, g32p_row03_traceSegment_065_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1417 34 34, g32p_row03_traceSegment_065_1417_0034, g32p_row03_traceSegment_065_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1350 67 68, g32p_row03_traceSegment_065_1350_0067, g32p_row03_traceSegment_065_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1501 8 9, g32p_row03_traceSegment_065_1501_0008, g32p_row03_traceSegment_065_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1485 16 17, g32p_row03_traceSegment_065_1485_0016, g32p_row03_traceSegment_065_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1518 8 9, g32p_row03_traceSegment_065_1518_0008, g32p_row03_traceSegment_065_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1535 8 9, g32p_row03_traceSegment_065_1535_0008, g32p_row03_traceSegment_065_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1518 17 17, g32p_row03_traceSegment_065_1518_0017, g32p_row03_traceSegment_065_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1485 33 34, g32p_row03_traceSegment_065_1485_0033, g32p_row03_traceSegment_065_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1552 8 9, g32p_row03_traceSegment_065_1552_0008, g32p_row03_traceSegment_065_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1569 8 9, g32p_row03_traceSegment_065_1569_0008, g32p_row03_traceSegment_065_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1552 17 17, g32p_row03_traceSegment_065_1552_0017, g32p_row03_traceSegment_065_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1586 8 9, g32p_row03_traceSegment_065_1586_0008, g32p_row03_traceSegment_065_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1603 8 9, g32p_row03_traceSegment_065_1603_0008, g32p_row03_traceSegment_065_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1586 17 17, g32p_row03_traceSegment_065_1586_0017, g32p_row03_traceSegment_065_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1552 34 34, g32p_row03_traceSegment_065_1552_0034, g32p_row03_traceSegment_065_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1485 67 68, g32p_row03_traceSegment_065_1485_0067, g32p_row03_traceSegment_065_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1350 135 135, g32p_row03_traceSegment_065_1350_0135, g32p_row03_traceSegment_065_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_065 1080 540 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1080 270 270, g32p_row03_traceSegment_065_1080_0270, g32p_row03_traceSegment_065_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1636 8 9, g32p_row03_traceSegment_065_1636_0008, g32p_row03_traceSegment_065_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1620 16 17, g32p_row03_traceSegment_065_1620_0016, g32p_row03_traceSegment_065_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1653 8 9, g32p_row03_traceSegment_065_1653_0008, g32p_row03_traceSegment_065_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1670 8 9, g32p_row03_traceSegment_065_1670_0008, g32p_row03_traceSegment_065_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1653 17 17, g32p_row03_traceSegment_065_1653_0017, g32p_row03_traceSegment_065_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1620 33 34, g32p_row03_traceSegment_065_1620_0033, g32p_row03_traceSegment_065_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1687 8 9, g32p_row03_traceSegment_065_1687_0008, g32p_row03_traceSegment_065_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1704 8 9, g32p_row03_traceSegment_065_1704_0008, g32p_row03_traceSegment_065_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1687 17 17, g32p_row03_traceSegment_065_1687_0017, g32p_row03_traceSegment_065_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1721 8 9, g32p_row03_traceSegment_065_1721_0008, g32p_row03_traceSegment_065_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1738 8 9, g32p_row03_traceSegment_065_1738_0008, g32p_row03_traceSegment_065_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1721 17 17, g32p_row03_traceSegment_065_1721_0017, g32p_row03_traceSegment_065_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1687 34 34, g32p_row03_traceSegment_065_1687_0034, g32p_row03_traceSegment_065_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1620 67 68, g32p_row03_traceSegment_065_1620_0067, g32p_row03_traceSegment_065_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1771 8 9, g32p_row03_traceSegment_065_1771_0008, g32p_row03_traceSegment_065_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1755 16 17, g32p_row03_traceSegment_065_1755_0016, g32p_row03_traceSegment_065_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1788 8 9, g32p_row03_traceSegment_065_1788_0008, g32p_row03_traceSegment_065_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1805 8 9, g32p_row03_traceSegment_065_1805_0008, g32p_row03_traceSegment_065_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1788 17 17, g32p_row03_traceSegment_065_1788_0017, g32p_row03_traceSegment_065_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1755 33 34, g32p_row03_traceSegment_065_1755_0033, g32p_row03_traceSegment_065_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1822 8 9, g32p_row03_traceSegment_065_1822_0008, g32p_row03_traceSegment_065_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1839 8 9, g32p_row03_traceSegment_065_1839_0008, g32p_row03_traceSegment_065_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1822 17 17, g32p_row03_traceSegment_065_1822_0017, g32p_row03_traceSegment_065_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1856 8 9, g32p_row03_traceSegment_065_1856_0008, g32p_row03_traceSegment_065_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1873 8 9, g32p_row03_traceSegment_065_1873_0008, g32p_row03_traceSegment_065_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1856 17 17, g32p_row03_traceSegment_065_1856_0017, g32p_row03_traceSegment_065_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1822 34 34, g32p_row03_traceSegment_065_1822_0034, g32p_row03_traceSegment_065_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1755 67 68, g32p_row03_traceSegment_065_1755_0067, g32p_row03_traceSegment_065_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1620 135 135, g32p_row03_traceSegment_065_1620_0135, g32p_row03_traceSegment_065_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1906 8 9, g32p_row03_traceSegment_065_1906_0008, g32p_row03_traceSegment_065_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1890 16 17, g32p_row03_traceSegment_065_1890_0016, g32p_row03_traceSegment_065_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1923 8 9, g32p_row03_traceSegment_065_1923_0008, g32p_row03_traceSegment_065_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1940 8 9, g32p_row03_traceSegment_065_1940_0008, g32p_row03_traceSegment_065_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1923 17 17, g32p_row03_traceSegment_065_1923_0017, g32p_row03_traceSegment_065_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1890 33 34, g32p_row03_traceSegment_065_1890_0033, g32p_row03_traceSegment_065_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1957 8 9, g32p_row03_traceSegment_065_1957_0008, g32p_row03_traceSegment_065_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1974 8 9, g32p_row03_traceSegment_065_1974_0008, g32p_row03_traceSegment_065_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1957 17 17, g32p_row03_traceSegment_065_1957_0017, g32p_row03_traceSegment_065_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1991 8 9, g32p_row03_traceSegment_065_1991_0008, g32p_row03_traceSegment_065_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2008 8 9, g32p_row03_traceSegment_065_2008_0008, g32p_row03_traceSegment_065_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1991 17 17, g32p_row03_traceSegment_065_1991_0017, g32p_row03_traceSegment_065_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1957 34 34, g32p_row03_traceSegment_065_1957_0034, g32p_row03_traceSegment_065_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1890 67 68, g32p_row03_traceSegment_065_1890_0067, g32p_row03_traceSegment_065_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2041 8 9, g32p_row03_traceSegment_065_2041_0008, g32p_row03_traceSegment_065_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2025 16 17, g32p_row03_traceSegment_065_2025_0016, g32p_row03_traceSegment_065_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2058 8 9, g32p_row03_traceSegment_065_2058_0008, g32p_row03_traceSegment_065_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2075 8 9, g32p_row03_traceSegment_065_2075_0008, g32p_row03_traceSegment_065_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2058 17 17, g32p_row03_traceSegment_065_2058_0017, g32p_row03_traceSegment_065_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2025 33 34, g32p_row03_traceSegment_065_2025_0033, g32p_row03_traceSegment_065_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2092 8 9, g32p_row03_traceSegment_065_2092_0008, g32p_row03_traceSegment_065_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2109 8 9, g32p_row03_traceSegment_065_2109_0008, g32p_row03_traceSegment_065_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2092 17 17, g32p_row03_traceSegment_065_2092_0017, g32p_row03_traceSegment_065_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2126 8 9, g32p_row03_traceSegment_065_2126_0008, g32p_row03_traceSegment_065_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2143 8 9, g32p_row03_traceSegment_065_2143_0008, g32p_row03_traceSegment_065_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2126 17 17, g32p_row03_traceSegment_065_2126_0017, g32p_row03_traceSegment_065_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2092 34 34, g32p_row03_traceSegment_065_2092_0034, g32p_row03_traceSegment_065_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2025 67 68, g32p_row03_traceSegment_065_2025_0067, g32p_row03_traceSegment_065_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 1890 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1890 135 135, g32p_row03_traceSegment_065_1890_0135, g32p_row03_traceSegment_065_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_065 1620 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1620 270 270, g32p_row03_traceSegment_065_1620_0270, g32p_row03_traceSegment_065_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_065_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_065 1080 1080 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 1080 540 540, g32p_row03_traceSegment_065_1080_0540, g32p_row03_traceSegment_065_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_065 0 2160 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 0 1080 1080, g32p_row03_traceSegment_065_0000_1080, g32p_row03_traceSegment_065_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2176 8 9, g32p_row03_traceSegment_065_2176_0008, g32p_row03_traceSegment_065_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2160 16 17, g32p_row03_traceSegment_065_2160_0016, g32p_row03_traceSegment_065_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2193 8 9, g32p_row03_traceSegment_065_2193_0008, g32p_row03_traceSegment_065_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2218 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2210 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2210 8 9, g32p_row03_traceSegment_065_2210_0008, g32p_row03_traceSegment_065_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2193 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2193 17 17, g32p_row03_traceSegment_065_2193_0017, g32p_row03_traceSegment_065_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 2160 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2160 33 34, g32p_row03_traceSegment_065_2160_0033, g32p_row03_traceSegment_065_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2227 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2227 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2227 8 9, g32p_row03_traceSegment_065_2227_0008, g32p_row03_traceSegment_065_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2244 8 9, g32p_row03_traceSegment_065_2244_0008, g32p_row03_traceSegment_065_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2227 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2227 17 17, g32p_row03_traceSegment_065_2227_0017, g32p_row03_traceSegment_065_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2261 8 9, g32p_row03_traceSegment_065_2261_0008, g32p_row03_traceSegment_065_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2278 8 9, g32p_row03_traceSegment_065_2278_0008, g32p_row03_traceSegment_065_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2261 17 17, g32p_row03_traceSegment_065_2261_0017, g32p_row03_traceSegment_065_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 2227 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2227 34 34, g32p_row03_traceSegment_065_2227_0034, g32p_row03_traceSegment_065_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 2160 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2160 67 68, g32p_row03_traceSegment_065_2160_0067, g32p_row03_traceSegment_065_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2311 8 9, g32p_row03_traceSegment_065_2311_0008, g32p_row03_traceSegment_065_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2295 16 17, g32p_row03_traceSegment_065_2295_0016, g32p_row03_traceSegment_065_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2336 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2328 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2328 8 9, g32p_row03_traceSegment_065_2328_0008, g32p_row03_traceSegment_065_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2345 8 9, g32p_row03_traceSegment_065_2345_0008, g32p_row03_traceSegment_065_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2328 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2328 17 17, g32p_row03_traceSegment_065_2328_0017, g32p_row03_traceSegment_065_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 2295 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2295 33 34, g32p_row03_traceSegment_065_2295_0033, g32p_row03_traceSegment_065_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2362 8 9, g32p_row03_traceSegment_065_2362_0008, g32p_row03_traceSegment_065_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2379 8 9, g32p_row03_traceSegment_065_2379_0008, g32p_row03_traceSegment_065_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2362 17 17, g32p_row03_traceSegment_065_2362_0017, g32p_row03_traceSegment_065_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2396 8 9, g32p_row03_traceSegment_065_2396_0008, g32p_row03_traceSegment_065_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2413 8 9, g32p_row03_traceSegment_065_2413_0008, g32p_row03_traceSegment_065_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2396 17 17, g32p_row03_traceSegment_065_2396_0017, g32p_row03_traceSegment_065_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2362 34 34, g32p_row03_traceSegment_065_2362_0034, g32p_row03_traceSegment_065_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 2295 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2295 67 68, g32p_row03_traceSegment_065_2295_0067, g32p_row03_traceSegment_065_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 2160 270 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2160 135 135, g32p_row03_traceSegment_065_2160_0135, g32p_row03_traceSegment_065_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 2430 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2446 8 9, g32p_row03_traceSegment_065_2446_0008, g32p_row03_traceSegment_065_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 2430 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2430 16 17, g32p_row03_traceSegment_065_2430_0016, g32p_row03_traceSegment_065_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2463 8 9, g32p_row03_traceSegment_065_2463_0008, g32p_row03_traceSegment_065_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2480 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2480 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2480 8 9, g32p_row03_traceSegment_065_2480_0008, g32p_row03_traceSegment_065_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2463 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2463 17 17, g32p_row03_traceSegment_065_2463_0017, g32p_row03_traceSegment_065_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 2430 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2430 33 34, g32p_row03_traceSegment_065_2430_0033, g32p_row03_traceSegment_065_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2497 8 9, g32p_row03_traceSegment_065_2497_0008, g32p_row03_traceSegment_065_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2514 8 9, g32p_row03_traceSegment_065_2514_0008, g32p_row03_traceSegment_065_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2497 17 17, g32p_row03_traceSegment_065_2497_0017, g32p_row03_traceSegment_065_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2531 8 9, g32p_row03_traceSegment_065_2531_0008, g32p_row03_traceSegment_065_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2548 8 9, g32p_row03_traceSegment_065_2548_0008, g32p_row03_traceSegment_065_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2531 17 17, g32p_row03_traceSegment_065_2531_0017, g32p_row03_traceSegment_065_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2497 34 34, g32p_row03_traceSegment_065_2497_0034, g32p_row03_traceSegment_065_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 2430 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2430 67 68, g32p_row03_traceSegment_065_2430_0067, g32p_row03_traceSegment_065_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 2565 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2581 8 9, g32p_row03_traceSegment_065_2581_0008, g32p_row03_traceSegment_065_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 2565 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2565 16 17, g32p_row03_traceSegment_065_2565_0016, g32p_row03_traceSegment_065_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2598 8 9, g32p_row03_traceSegment_065_2598_0008, g32p_row03_traceSegment_065_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2615 8 9, g32p_row03_traceSegment_065_2615_0008, g32p_row03_traceSegment_065_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2598 17 17, g32p_row03_traceSegment_065_2598_0017, g32p_row03_traceSegment_065_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 2565 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2565 33 34, g32p_row03_traceSegment_065_2565_0033, g32p_row03_traceSegment_065_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2632 8 9, g32p_row03_traceSegment_065_2632_0008, g32p_row03_traceSegment_065_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2649 8 9, g32p_row03_traceSegment_065_2649_0008, g32p_row03_traceSegment_065_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2632 17 17, g32p_row03_traceSegment_065_2632_0017, g32p_row03_traceSegment_065_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2666 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2666 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2666 8 9, g32p_row03_traceSegment_065_2666_0008, g32p_row03_traceSegment_065_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2683 8 9, g32p_row03_traceSegment_065_2683_0008, g32p_row03_traceSegment_065_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2666 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2666 17 17, g32p_row03_traceSegment_065_2666_0017, g32p_row03_traceSegment_065_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 2632 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2632 34 34, g32p_row03_traceSegment_065_2632_0034, g32p_row03_traceSegment_065_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 2565 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2565 67 68, g32p_row03_traceSegment_065_2565_0067, g32p_row03_traceSegment_065_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 2430 270 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2430 135 135, g32p_row03_traceSegment_065_2430_0135, g32p_row03_traceSegment_065_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_065 2160 540 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2160 270 270, g32p_row03_traceSegment_065_2160_0270, g32p_row03_traceSegment_065_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2716 8 9, g32p_row03_traceSegment_065_2716_0008, g32p_row03_traceSegment_065_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2700 16 17, g32p_row03_traceSegment_065_2700_0016, g32p_row03_traceSegment_065_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2733 8 9, g32p_row03_traceSegment_065_2733_0008, g32p_row03_traceSegment_065_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2750 8 9, g32p_row03_traceSegment_065_2750_0008, g32p_row03_traceSegment_065_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2733 17 17, g32p_row03_traceSegment_065_2733_0017, g32p_row03_traceSegment_065_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2700 33 34, g32p_row03_traceSegment_065_2700_0033, g32p_row03_traceSegment_065_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2767 8 9, g32p_row03_traceSegment_065_2767_0008, g32p_row03_traceSegment_065_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2784 8 9, g32p_row03_traceSegment_065_2784_0008, g32p_row03_traceSegment_065_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2767 17 17, g32p_row03_traceSegment_065_2767_0017, g32p_row03_traceSegment_065_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2801 8 9, g32p_row03_traceSegment_065_2801_0008, g32p_row03_traceSegment_065_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2826 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2818 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2818 8 9, g32p_row03_traceSegment_065_2818_0008, g32p_row03_traceSegment_065_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2801 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2801 17 17, g32p_row03_traceSegment_065_2801_0017, g32p_row03_traceSegment_065_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 2767 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2767 34 34, g32p_row03_traceSegment_065_2767_0034, g32p_row03_traceSegment_065_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 2700 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2700 67 68, g32p_row03_traceSegment_065_2700_0067, g32p_row03_traceSegment_065_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2851 8 9, g32p_row03_traceSegment_065_2851_0008, g32p_row03_traceSegment_065_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2835 16 17, g32p_row03_traceSegment_065_2835_0016, g32p_row03_traceSegment_065_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2868 8 9, g32p_row03_traceSegment_065_2868_0008, g32p_row03_traceSegment_065_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2885 8 9, g32p_row03_traceSegment_065_2885_0008, g32p_row03_traceSegment_065_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2868 17 17, g32p_row03_traceSegment_065_2868_0017, g32p_row03_traceSegment_065_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2835 33 34, g32p_row03_traceSegment_065_2835_0033, g32p_row03_traceSegment_065_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2902 8 9, g32p_row03_traceSegment_065_2902_0008, g32p_row03_traceSegment_065_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2919 8 9, g32p_row03_traceSegment_065_2919_0008, g32p_row03_traceSegment_065_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2902 17 17, g32p_row03_traceSegment_065_2902_0017, g32p_row03_traceSegment_065_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2936 8 9, g32p_row03_traceSegment_065_2936_0008, g32p_row03_traceSegment_065_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2953 8 9, g32p_row03_traceSegment_065_2953_0008, g32p_row03_traceSegment_065_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2936 17 17, g32p_row03_traceSegment_065_2936_0017, g32p_row03_traceSegment_065_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2902 34 34, g32p_row03_traceSegment_065_2902_0034, g32p_row03_traceSegment_065_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2835 67 68, g32p_row03_traceSegment_065_2835_0067, g32p_row03_traceSegment_065_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 2700 270 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2700 135 135, g32p_row03_traceSegment_065_2700_0135, g32p_row03_traceSegment_065_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2986 8 9, g32p_row03_traceSegment_065_2986_0008, g32p_row03_traceSegment_065_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2970 16 17, g32p_row03_traceSegment_065_2970_0016, g32p_row03_traceSegment_065_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3003 8 9, g32p_row03_traceSegment_065_3003_0008, g32p_row03_traceSegment_065_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3020 8 9, g32p_row03_traceSegment_065_3020_0008, g32p_row03_traceSegment_065_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3003 17 17, g32p_row03_traceSegment_065_3003_0017, g32p_row03_traceSegment_065_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2970 33 34, g32p_row03_traceSegment_065_2970_0033, g32p_row03_traceSegment_065_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3037 8 9, g32p_row03_traceSegment_065_3037_0008, g32p_row03_traceSegment_065_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3054 8 9, g32p_row03_traceSegment_065_3054_0008, g32p_row03_traceSegment_065_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3037 17 17, g32p_row03_traceSegment_065_3037_0017, g32p_row03_traceSegment_065_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3071 8 9, g32p_row03_traceSegment_065_3071_0008, g32p_row03_traceSegment_065_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3088 8 9, g32p_row03_traceSegment_065_3088_0008, g32p_row03_traceSegment_065_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3071 17 17, g32p_row03_traceSegment_065_3071_0017, g32p_row03_traceSegment_065_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3037 34 34, g32p_row03_traceSegment_065_3037_0034, g32p_row03_traceSegment_065_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2970 67 68, g32p_row03_traceSegment_065_2970_0067, g32p_row03_traceSegment_065_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3121 8 9, g32p_row03_traceSegment_065_3121_0008, g32p_row03_traceSegment_065_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3105 16 17, g32p_row03_traceSegment_065_3105_0016, g32p_row03_traceSegment_065_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3138 8 9, g32p_row03_traceSegment_065_3138_0008, g32p_row03_traceSegment_065_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3155 8 9, g32p_row03_traceSegment_065_3155_0008, g32p_row03_traceSegment_065_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3138 17 17, g32p_row03_traceSegment_065_3138_0017, g32p_row03_traceSegment_065_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3105 33 34, g32p_row03_traceSegment_065_3105_0033, g32p_row03_traceSegment_065_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3172 8 9, g32p_row03_traceSegment_065_3172_0008, g32p_row03_traceSegment_065_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3189 8 9, g32p_row03_traceSegment_065_3189_0008, g32p_row03_traceSegment_065_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3172 17 17, g32p_row03_traceSegment_065_3172_0017, g32p_row03_traceSegment_065_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3206 8 9, g32p_row03_traceSegment_065_3206_0008, g32p_row03_traceSegment_065_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3223 8 9, g32p_row03_traceSegment_065_3223_0008, g32p_row03_traceSegment_065_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3206 17 17, g32p_row03_traceSegment_065_3206_0017, g32p_row03_traceSegment_065_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3172 34 34, g32p_row03_traceSegment_065_3172_0034, g32p_row03_traceSegment_065_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3105 67 68, g32p_row03_traceSegment_065_3105_0067, g32p_row03_traceSegment_065_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2970 135 135, g32p_row03_traceSegment_065_2970_0135, g32p_row03_traceSegment_065_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_065 2700 540 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2700 270 270, g32p_row03_traceSegment_065_2700_0270, g32p_row03_traceSegment_065_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_065 2160 1080 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2160 540 540, g32p_row03_traceSegment_065_2160_0540, g32p_row03_traceSegment_065_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3256 8 9, g32p_row03_traceSegment_065_3256_0008, g32p_row03_traceSegment_065_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3240 16 17, g32p_row03_traceSegment_065_3240_0016, g32p_row03_traceSegment_065_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3273 8 9, g32p_row03_traceSegment_065_3273_0008, g32p_row03_traceSegment_065_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3290 8 9, g32p_row03_traceSegment_065_3290_0008, g32p_row03_traceSegment_065_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3273 17 17, g32p_row03_traceSegment_065_3273_0017, g32p_row03_traceSegment_065_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3240 33 34, g32p_row03_traceSegment_065_3240_0033, g32p_row03_traceSegment_065_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3307 8 9, g32p_row03_traceSegment_065_3307_0008, g32p_row03_traceSegment_065_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3324 8 9, g32p_row03_traceSegment_065_3324_0008, g32p_row03_traceSegment_065_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3307 17 17, g32p_row03_traceSegment_065_3307_0017, g32p_row03_traceSegment_065_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3341 8 9, g32p_row03_traceSegment_065_3341_0008, g32p_row03_traceSegment_065_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3358 8 9, g32p_row03_traceSegment_065_3358_0008, g32p_row03_traceSegment_065_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3341 17 17, g32p_row03_traceSegment_065_3341_0017, g32p_row03_traceSegment_065_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3307 34 34, g32p_row03_traceSegment_065_3307_0034, g32p_row03_traceSegment_065_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3240 67 68, g32p_row03_traceSegment_065_3240_0067, g32p_row03_traceSegment_065_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3391 8 9, g32p_row03_traceSegment_065_3391_0008, g32p_row03_traceSegment_065_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3375 16 17, g32p_row03_traceSegment_065_3375_0016, g32p_row03_traceSegment_065_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3408 8 9, g32p_row03_traceSegment_065_3408_0008, g32p_row03_traceSegment_065_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3425 8 9, g32p_row03_traceSegment_065_3425_0008, g32p_row03_traceSegment_065_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3408 17 17, g32p_row03_traceSegment_065_3408_0017, g32p_row03_traceSegment_065_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3375 33 34, g32p_row03_traceSegment_065_3375_0033, g32p_row03_traceSegment_065_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3442 8 9, g32p_row03_traceSegment_065_3442_0008, g32p_row03_traceSegment_065_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3459 8 9, g32p_row03_traceSegment_065_3459_0008, g32p_row03_traceSegment_065_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3442 17 17, g32p_row03_traceSegment_065_3442_0017, g32p_row03_traceSegment_065_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3476 8 9, g32p_row03_traceSegment_065_3476_0008, g32p_row03_traceSegment_065_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3493 8 9, g32p_row03_traceSegment_065_3493_0008, g32p_row03_traceSegment_065_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3476 17 17, g32p_row03_traceSegment_065_3476_0017, g32p_row03_traceSegment_065_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3442 34 34, g32p_row03_traceSegment_065_3442_0034, g32p_row03_traceSegment_065_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3375 67 68, g32p_row03_traceSegment_065_3375_0067, g32p_row03_traceSegment_065_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3240 135 135, g32p_row03_traceSegment_065_3240_0135, g32p_row03_traceSegment_065_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3526 8 9, g32p_row03_traceSegment_065_3526_0008, g32p_row03_traceSegment_065_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3510 16 17, g32p_row03_traceSegment_065_3510_0016, g32p_row03_traceSegment_065_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3543 8 9, g32p_row03_traceSegment_065_3543_0008, g32p_row03_traceSegment_065_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3560 8 9, g32p_row03_traceSegment_065_3560_0008, g32p_row03_traceSegment_065_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3543 17 17, g32p_row03_traceSegment_065_3543_0017, g32p_row03_traceSegment_065_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3510 33 34, g32p_row03_traceSegment_065_3510_0033, g32p_row03_traceSegment_065_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3577 8 9, g32p_row03_traceSegment_065_3577_0008, g32p_row03_traceSegment_065_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3594 8 9, g32p_row03_traceSegment_065_3594_0008, g32p_row03_traceSegment_065_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3577 17 17, g32p_row03_traceSegment_065_3577_0017, g32p_row03_traceSegment_065_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3611 8 9, g32p_row03_traceSegment_065_3611_0008, g32p_row03_traceSegment_065_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3628 8 9, g32p_row03_traceSegment_065_3628_0008, g32p_row03_traceSegment_065_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3611 17 17, g32p_row03_traceSegment_065_3611_0017, g32p_row03_traceSegment_065_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3577 34 34, g32p_row03_traceSegment_065_3577_0034, g32p_row03_traceSegment_065_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3510 67 68, g32p_row03_traceSegment_065_3510_0067, g32p_row03_traceSegment_065_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3661 8 9, g32p_row03_traceSegment_065_3661_0008, g32p_row03_traceSegment_065_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3645 16 17, g32p_row03_traceSegment_065_3645_0016, g32p_row03_traceSegment_065_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3678 8 9, g32p_row03_traceSegment_065_3678_0008, g32p_row03_traceSegment_065_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3695 8 9, g32p_row03_traceSegment_065_3695_0008, g32p_row03_traceSegment_065_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3678 17 17, g32p_row03_traceSegment_065_3678_0017, g32p_row03_traceSegment_065_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3645 33 34, g32p_row03_traceSegment_065_3645_0033, g32p_row03_traceSegment_065_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3712 8 9, g32p_row03_traceSegment_065_3712_0008, g32p_row03_traceSegment_065_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3729 8 9, g32p_row03_traceSegment_065_3729_0008, g32p_row03_traceSegment_065_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3712 17 17, g32p_row03_traceSegment_065_3712_0017, g32p_row03_traceSegment_065_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3754 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3746 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3746 8 9, g32p_row03_traceSegment_065_3746_0008, g32p_row03_traceSegment_065_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3771 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3763 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3763 8 9, g32p_row03_traceSegment_065_3763_0008, g32p_row03_traceSegment_065_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3746 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3746 17 17, g32p_row03_traceSegment_065_3746_0017, g32p_row03_traceSegment_065_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 3712 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3712 34 34, g32p_row03_traceSegment_065_3712_0034, g32p_row03_traceSegment_065_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 3645 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3645 67 68, g32p_row03_traceSegment_065_3645_0067, g32p_row03_traceSegment_065_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 3510 270 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3510 135 135, g32p_row03_traceSegment_065_3510_0135, g32p_row03_traceSegment_065_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_065 3240 540 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3240 270 270, g32p_row03_traceSegment_065_3240_0270, g32p_row03_traceSegment_065_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3796 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3796 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3796 8 9, g32p_row03_traceSegment_065_3796_0008, g32p_row03_traceSegment_065_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 3780 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3780 16 17, g32p_row03_traceSegment_065_3780_0016, g32p_row03_traceSegment_065_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3813 8 9, g32p_row03_traceSegment_065_3813_0008, g32p_row03_traceSegment_065_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3830 8 9, g32p_row03_traceSegment_065_3830_0008, g32p_row03_traceSegment_065_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3813 17 17, g32p_row03_traceSegment_065_3813_0017, g32p_row03_traceSegment_065_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 3780 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3780 33 34, g32p_row03_traceSegment_065_3780_0033, g32p_row03_traceSegment_065_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3847 8 9, g32p_row03_traceSegment_065_3847_0008, g32p_row03_traceSegment_065_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3864 8 9, g32p_row03_traceSegment_065_3864_0008, g32p_row03_traceSegment_065_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3847 17 17, g32p_row03_traceSegment_065_3847_0017, g32p_row03_traceSegment_065_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3881 8 9, g32p_row03_traceSegment_065_3881_0008, g32p_row03_traceSegment_065_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3898 8 9, g32p_row03_traceSegment_065_3898_0008, g32p_row03_traceSegment_065_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3881 17 17, g32p_row03_traceSegment_065_3881_0017, g32p_row03_traceSegment_065_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3847 34 34, g32p_row03_traceSegment_065_3847_0034, g32p_row03_traceSegment_065_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 3780 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3780 67 68, g32p_row03_traceSegment_065_3780_0067, g32p_row03_traceSegment_065_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3931 8 9, g32p_row03_traceSegment_065_3931_0008, g32p_row03_traceSegment_065_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3915 16 17, g32p_row03_traceSegment_065_3915_0016, g32p_row03_traceSegment_065_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3948 8 9, g32p_row03_traceSegment_065_3948_0008, g32p_row03_traceSegment_065_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3965 8 9, g32p_row03_traceSegment_065_3965_0008, g32p_row03_traceSegment_065_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3948 17 17, g32p_row03_traceSegment_065_3948_0017, g32p_row03_traceSegment_065_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3915 33 34, g32p_row03_traceSegment_065_3915_0033, g32p_row03_traceSegment_065_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3982 8 9, g32p_row03_traceSegment_065_3982_0008, g32p_row03_traceSegment_065_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3999 8 9, g32p_row03_traceSegment_065_3999_0008, g32p_row03_traceSegment_065_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3982 17 17, g32p_row03_traceSegment_065_3982_0017, g32p_row03_traceSegment_065_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4016 8 9, g32p_row03_traceSegment_065_4016_0008, g32p_row03_traceSegment_065_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4033 8 9, g32p_row03_traceSegment_065_4033_0008, g32p_row03_traceSegment_065_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4016 17 17, g32p_row03_traceSegment_065_4016_0017, g32p_row03_traceSegment_065_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3982 34 34, g32p_row03_traceSegment_065_3982_0034, g32p_row03_traceSegment_065_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3915 67 68, g32p_row03_traceSegment_065_3915_0067, g32p_row03_traceSegment_065_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 3780 270 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3780 135 135, g32p_row03_traceSegment_065_3780_0135, g32p_row03_traceSegment_065_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4066 8 9, g32p_row03_traceSegment_065_4066_0008, g32p_row03_traceSegment_065_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4050 16 17, g32p_row03_traceSegment_065_4050_0016, g32p_row03_traceSegment_065_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4083 8 9, g32p_row03_traceSegment_065_4083_0008, g32p_row03_traceSegment_065_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4100 8 9, g32p_row03_traceSegment_065_4100_0008, g32p_row03_traceSegment_065_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4083 17 17, g32p_row03_traceSegment_065_4083_0017, g32p_row03_traceSegment_065_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4050 33 34, g32p_row03_traceSegment_065_4050_0033, g32p_row03_traceSegment_065_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4117 8 9, g32p_row03_traceSegment_065_4117_0008, g32p_row03_traceSegment_065_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4134 8 9, g32p_row03_traceSegment_065_4134_0008, g32p_row03_traceSegment_065_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4117 17 17, g32p_row03_traceSegment_065_4117_0017, g32p_row03_traceSegment_065_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4151 8 9, g32p_row03_traceSegment_065_4151_0008, g32p_row03_traceSegment_065_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4168 8 9, g32p_row03_traceSegment_065_4168_0008, g32p_row03_traceSegment_065_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4151 17 17, g32p_row03_traceSegment_065_4151_0017, g32p_row03_traceSegment_065_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4117 34 34, g32p_row03_traceSegment_065_4117_0034, g32p_row03_traceSegment_065_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4050 67 68, g32p_row03_traceSegment_065_4050_0067, g32p_row03_traceSegment_065_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_065 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4201 8 9, g32p_row03_traceSegment_065_4201_0008, g32p_row03_traceSegment_065_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_065 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4185 16 17, g32p_row03_traceSegment_065_4185_0016, g32p_row03_traceSegment_065_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4218 8 9, g32p_row03_traceSegment_065_4218_0008, g32p_row03_traceSegment_065_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4235 8 9, g32p_row03_traceSegment_065_4235_0008, g32p_row03_traceSegment_065_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4218 17 17, g32p_row03_traceSegment_065_4218_0017, g32p_row03_traceSegment_065_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_065 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4185 33 34, g32p_row03_traceSegment_065_4185_0033, g32p_row03_traceSegment_065_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4252 8 9, g32p_row03_traceSegment_065_4252_0008, g32p_row03_traceSegment_065_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4277 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4269 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4269 8 9, g32p_row03_traceSegment_065_4269_0008, g32p_row03_traceSegment_065_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 4252 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4252 17 17, g32p_row03_traceSegment_065_4252_0017, g32p_row03_traceSegment_065_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4294 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4286 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4286 8 9, g32p_row03_traceSegment_065_4286_0008, g32p_row03_traceSegment_065_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_065 4303 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_065 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_065_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_065 4303 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4303 8 9, g32p_row03_traceSegment_065_4303_0008, g32p_row03_traceSegment_065_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_065 4286 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4286 17 17, g32p_row03_traceSegment_065_4286_0017, g32p_row03_traceSegment_065_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_065 4252 68 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4252 34 34, g32p_row03_traceSegment_065_4252_0034, g32p_row03_traceSegment_065_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_065 4185 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4185 67 68, g32p_row03_traceSegment_065_4185_0067, g32p_row03_traceSegment_065_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_065_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_065 4050 270 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 4050 135 135, g32p_row03_traceSegment_065_4050_0135, g32p_row03_traceSegment_065_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_065 3780 540 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3780 270 270, g32p_row03_traceSegment_065_3780_0270, g32p_row03_traceSegment_065_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_065_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_065 3240 1080 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 3240 540 540, g32p_row03_traceSegment_065_3240_0540, g32p_row03_traceSegment_065_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_065_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_065 2160 2160 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 2160 1080 1080, g32p_row03_traceSegment_065_2160_1080, g32p_row03_traceSegment_065_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_065_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_065 0 4320 = [0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_065 0 2160 2160, g32p_row03_traceSegment_065_0000_2160, g32p_row03_traceSegment_065_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 65 = [0, 30] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_065_0000_4320

end HodgeLean.Foundations.Program

end
end
