import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_082 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 82 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_082_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 16 8 9, g32p_row03_traceSegment_082_0016_0008, g32p_row03_traceSegment_082_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 0 16 17, g32p_row03_traceSegment_082_0000_0016, g32p_row03_traceSegment_082_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 33 8 9, g32p_row03_traceSegment_082_0033_0008, g32p_row03_traceSegment_082_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 50 8 9, g32p_row03_traceSegment_082_0050_0008, g32p_row03_traceSegment_082_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 33 17 17, g32p_row03_traceSegment_082_0033_0017, g32p_row03_traceSegment_082_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 0 33 34, g32p_row03_traceSegment_082_0000_0033, g32p_row03_traceSegment_082_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 67 8 9, g32p_row03_traceSegment_082_0067_0008, g32p_row03_traceSegment_082_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 84 8 9, g32p_row03_traceSegment_082_0084_0008, g32p_row03_traceSegment_082_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 67 17 17, g32p_row03_traceSegment_082_0067_0017, g32p_row03_traceSegment_082_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 101 8 9, g32p_row03_traceSegment_082_0101_0008, g32p_row03_traceSegment_082_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 118 8 9, g32p_row03_traceSegment_082_0118_0008, g32p_row03_traceSegment_082_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 101 17 17, g32p_row03_traceSegment_082_0101_0017, g32p_row03_traceSegment_082_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 67 34 34, g32p_row03_traceSegment_082_0067_0034, g32p_row03_traceSegment_082_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 0 67 68, g32p_row03_traceSegment_082_0000_0067, g32p_row03_traceSegment_082_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 151 8 9, g32p_row03_traceSegment_082_0151_0008, g32p_row03_traceSegment_082_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 135 16 17, g32p_row03_traceSegment_082_0135_0016, g32p_row03_traceSegment_082_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 168 8 9, g32p_row03_traceSegment_082_0168_0008, g32p_row03_traceSegment_082_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 185 8 9, g32p_row03_traceSegment_082_0185_0008, g32p_row03_traceSegment_082_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 168 17 17, g32p_row03_traceSegment_082_0168_0017, g32p_row03_traceSegment_082_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 135 33 34, g32p_row03_traceSegment_082_0135_0033, g32p_row03_traceSegment_082_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 202 8 9, g32p_row03_traceSegment_082_0202_0008, g32p_row03_traceSegment_082_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 219 8 9, g32p_row03_traceSegment_082_0219_0008, g32p_row03_traceSegment_082_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 202 17 17, g32p_row03_traceSegment_082_0202_0017, g32p_row03_traceSegment_082_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 236 8 9, g32p_row03_traceSegment_082_0236_0008, g32p_row03_traceSegment_082_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 253 8 9, g32p_row03_traceSegment_082_0253_0008, g32p_row03_traceSegment_082_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 236 17 17, g32p_row03_traceSegment_082_0236_0017, g32p_row03_traceSegment_082_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 202 34 34, g32p_row03_traceSegment_082_0202_0034, g32p_row03_traceSegment_082_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 135 67 68, g32p_row03_traceSegment_082_0135_0067, g32p_row03_traceSegment_082_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 0 135 135, g32p_row03_traceSegment_082_0000_0135, g32p_row03_traceSegment_082_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 286 8 9, g32p_row03_traceSegment_082_0286_0008, g32p_row03_traceSegment_082_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 270 16 17, g32p_row03_traceSegment_082_0270_0016, g32p_row03_traceSegment_082_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 303 8 9, g32p_row03_traceSegment_082_0303_0008, g32p_row03_traceSegment_082_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 320 8 9, g32p_row03_traceSegment_082_0320_0008, g32p_row03_traceSegment_082_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 303 17 17, g32p_row03_traceSegment_082_0303_0017, g32p_row03_traceSegment_082_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 270 33 34, g32p_row03_traceSegment_082_0270_0033, g32p_row03_traceSegment_082_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 337 8 9, g32p_row03_traceSegment_082_0337_0008, g32p_row03_traceSegment_082_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 354 8 9, g32p_row03_traceSegment_082_0354_0008, g32p_row03_traceSegment_082_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 337 17 17, g32p_row03_traceSegment_082_0337_0017, g32p_row03_traceSegment_082_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 371 8 9, g32p_row03_traceSegment_082_0371_0008, g32p_row03_traceSegment_082_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 388 8 9, g32p_row03_traceSegment_082_0388_0008, g32p_row03_traceSegment_082_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 371 17 17, g32p_row03_traceSegment_082_0371_0017, g32p_row03_traceSegment_082_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 337 34 34, g32p_row03_traceSegment_082_0337_0034, g32p_row03_traceSegment_082_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 270 67 68, g32p_row03_traceSegment_082_0270_0067, g32p_row03_traceSegment_082_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 421 8 9, g32p_row03_traceSegment_082_0421_0008, g32p_row03_traceSegment_082_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 405 16 17, g32p_row03_traceSegment_082_0405_0016, g32p_row03_traceSegment_082_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 438 8 9, g32p_row03_traceSegment_082_0438_0008, g32p_row03_traceSegment_082_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 455 8 9, g32p_row03_traceSegment_082_0455_0008, g32p_row03_traceSegment_082_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 438 17 17, g32p_row03_traceSegment_082_0438_0017, g32p_row03_traceSegment_082_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 405 33 34, g32p_row03_traceSegment_082_0405_0033, g32p_row03_traceSegment_082_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 472 8 9, g32p_row03_traceSegment_082_0472_0008, g32p_row03_traceSegment_082_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 489 8 9, g32p_row03_traceSegment_082_0489_0008, g32p_row03_traceSegment_082_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 472 17 17, g32p_row03_traceSegment_082_0472_0017, g32p_row03_traceSegment_082_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 506 8 9, g32p_row03_traceSegment_082_0506_0008, g32p_row03_traceSegment_082_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 523 8 9, g32p_row03_traceSegment_082_0523_0008, g32p_row03_traceSegment_082_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 506 17 17, g32p_row03_traceSegment_082_0506_0017, g32p_row03_traceSegment_082_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 472 34 34, g32p_row03_traceSegment_082_0472_0034, g32p_row03_traceSegment_082_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 405 67 68, g32p_row03_traceSegment_082_0405_0067, g32p_row03_traceSegment_082_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 270 135 135, g32p_row03_traceSegment_082_0270_0135, g32p_row03_traceSegment_082_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_082 0 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 0 270 270, g32p_row03_traceSegment_082_0000_0270, g32p_row03_traceSegment_082_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 556 8 9, g32p_row03_traceSegment_082_0556_0008, g32p_row03_traceSegment_082_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 540 16 17, g32p_row03_traceSegment_082_0540_0016, g32p_row03_traceSegment_082_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 573 8 9, g32p_row03_traceSegment_082_0573_0008, g32p_row03_traceSegment_082_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 590 8 9, g32p_row03_traceSegment_082_0590_0008, g32p_row03_traceSegment_082_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 573 17 17, g32p_row03_traceSegment_082_0573_0017, g32p_row03_traceSegment_082_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 540 33 34, g32p_row03_traceSegment_082_0540_0033, g32p_row03_traceSegment_082_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 607 8 9, g32p_row03_traceSegment_082_0607_0008, g32p_row03_traceSegment_082_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 624 8 9, g32p_row03_traceSegment_082_0624_0008, g32p_row03_traceSegment_082_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 607 17 17, g32p_row03_traceSegment_082_0607_0017, g32p_row03_traceSegment_082_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 641 8 9, g32p_row03_traceSegment_082_0641_0008, g32p_row03_traceSegment_082_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 658 8 9, g32p_row03_traceSegment_082_0658_0008, g32p_row03_traceSegment_082_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 641 17 17, g32p_row03_traceSegment_082_0641_0017, g32p_row03_traceSegment_082_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 607 34 34, g32p_row03_traceSegment_082_0607_0034, g32p_row03_traceSegment_082_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 540 67 68, g32p_row03_traceSegment_082_0540_0067, g32p_row03_traceSegment_082_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 691 8 9, g32p_row03_traceSegment_082_0691_0008, g32p_row03_traceSegment_082_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 675 16 17, g32p_row03_traceSegment_082_0675_0016, g32p_row03_traceSegment_082_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 708 8 9, g32p_row03_traceSegment_082_0708_0008, g32p_row03_traceSegment_082_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 725 8 9, g32p_row03_traceSegment_082_0725_0008, g32p_row03_traceSegment_082_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 708 17 17, g32p_row03_traceSegment_082_0708_0017, g32p_row03_traceSegment_082_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 675 33 34, g32p_row03_traceSegment_082_0675_0033, g32p_row03_traceSegment_082_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 742 8 9, g32p_row03_traceSegment_082_0742_0008, g32p_row03_traceSegment_082_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 759 8 9, g32p_row03_traceSegment_082_0759_0008, g32p_row03_traceSegment_082_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 742 17 17, g32p_row03_traceSegment_082_0742_0017, g32p_row03_traceSegment_082_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 776 8 9, g32p_row03_traceSegment_082_0776_0008, g32p_row03_traceSegment_082_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 793 8 9, g32p_row03_traceSegment_082_0793_0008, g32p_row03_traceSegment_082_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 776 17 17, g32p_row03_traceSegment_082_0776_0017, g32p_row03_traceSegment_082_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 742 34 34, g32p_row03_traceSegment_082_0742_0034, g32p_row03_traceSegment_082_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 675 67 68, g32p_row03_traceSegment_082_0675_0067, g32p_row03_traceSegment_082_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 540 135 135, g32p_row03_traceSegment_082_0540_0135, g32p_row03_traceSegment_082_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 826 8 9, g32p_row03_traceSegment_082_0826_0008, g32p_row03_traceSegment_082_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 810 16 17, g32p_row03_traceSegment_082_0810_0016, g32p_row03_traceSegment_082_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 843 8 9, g32p_row03_traceSegment_082_0843_0008, g32p_row03_traceSegment_082_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 860 8 9, g32p_row03_traceSegment_082_0860_0008, g32p_row03_traceSegment_082_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 843 17 17, g32p_row03_traceSegment_082_0843_0017, g32p_row03_traceSegment_082_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 810 33 34, g32p_row03_traceSegment_082_0810_0033, g32p_row03_traceSegment_082_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 877 8 9, g32p_row03_traceSegment_082_0877_0008, g32p_row03_traceSegment_082_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 894 8 9, g32p_row03_traceSegment_082_0894_0008, g32p_row03_traceSegment_082_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 877 17 17, g32p_row03_traceSegment_082_0877_0017, g32p_row03_traceSegment_082_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 911 8 9, g32p_row03_traceSegment_082_0911_0008, g32p_row03_traceSegment_082_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 928 8 9, g32p_row03_traceSegment_082_0928_0008, g32p_row03_traceSegment_082_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 911 17 17, g32p_row03_traceSegment_082_0911_0017, g32p_row03_traceSegment_082_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 877 34 34, g32p_row03_traceSegment_082_0877_0034, g32p_row03_traceSegment_082_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 810 67 68, g32p_row03_traceSegment_082_0810_0067, g32p_row03_traceSegment_082_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 961 8 9, g32p_row03_traceSegment_082_0961_0008, g32p_row03_traceSegment_082_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 945 16 17, g32p_row03_traceSegment_082_0945_0016, g32p_row03_traceSegment_082_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 978 8 9, g32p_row03_traceSegment_082_0978_0008, g32p_row03_traceSegment_082_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 995 8 9, g32p_row03_traceSegment_082_0995_0008, g32p_row03_traceSegment_082_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 978 17 17, g32p_row03_traceSegment_082_0978_0017, g32p_row03_traceSegment_082_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 945 33 34, g32p_row03_traceSegment_082_0945_0033, g32p_row03_traceSegment_082_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1012 8 9, g32p_row03_traceSegment_082_1012_0008, g32p_row03_traceSegment_082_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1029 8 9, g32p_row03_traceSegment_082_1029_0008, g32p_row03_traceSegment_082_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1012 17 17, g32p_row03_traceSegment_082_1012_0017, g32p_row03_traceSegment_082_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1046 8 9, g32p_row03_traceSegment_082_1046_0008, g32p_row03_traceSegment_082_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1063 8 9, g32p_row03_traceSegment_082_1063_0008, g32p_row03_traceSegment_082_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1046 17 17, g32p_row03_traceSegment_082_1046_0017, g32p_row03_traceSegment_082_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1012 34 34, g32p_row03_traceSegment_082_1012_0034, g32p_row03_traceSegment_082_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 945 67 68, g32p_row03_traceSegment_082_0945_0067, g32p_row03_traceSegment_082_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 810 135 135, g32p_row03_traceSegment_082_0810_0135, g32p_row03_traceSegment_082_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_082 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 540 270 270, g32p_row03_traceSegment_082_0540_0270, g32p_row03_traceSegment_082_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_082 0 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 0 540 540, g32p_row03_traceSegment_082_0000_0540, g32p_row03_traceSegment_082_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1096 8 9, g32p_row03_traceSegment_082_1096_0008, g32p_row03_traceSegment_082_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1080 16 17, g32p_row03_traceSegment_082_1080_0016, g32p_row03_traceSegment_082_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1113 8 9, g32p_row03_traceSegment_082_1113_0008, g32p_row03_traceSegment_082_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1130 8 9, g32p_row03_traceSegment_082_1130_0008, g32p_row03_traceSegment_082_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1113 17 17, g32p_row03_traceSegment_082_1113_0017, g32p_row03_traceSegment_082_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1080 33 34, g32p_row03_traceSegment_082_1080_0033, g32p_row03_traceSegment_082_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1147 8 9, g32p_row03_traceSegment_082_1147_0008, g32p_row03_traceSegment_082_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1164 8 9, g32p_row03_traceSegment_082_1164_0008, g32p_row03_traceSegment_082_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1147 17 17, g32p_row03_traceSegment_082_1147_0017, g32p_row03_traceSegment_082_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1181 8 9, g32p_row03_traceSegment_082_1181_0008, g32p_row03_traceSegment_082_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1198 8 9, g32p_row03_traceSegment_082_1198_0008, g32p_row03_traceSegment_082_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1181 17 17, g32p_row03_traceSegment_082_1181_0017, g32p_row03_traceSegment_082_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1147 34 34, g32p_row03_traceSegment_082_1147_0034, g32p_row03_traceSegment_082_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1080 67 68, g32p_row03_traceSegment_082_1080_0067, g32p_row03_traceSegment_082_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1231 8 9, g32p_row03_traceSegment_082_1231_0008, g32p_row03_traceSegment_082_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1215 16 17, g32p_row03_traceSegment_082_1215_0016, g32p_row03_traceSegment_082_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1248 8 9, g32p_row03_traceSegment_082_1248_0008, g32p_row03_traceSegment_082_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1265 8 9, g32p_row03_traceSegment_082_1265_0008, g32p_row03_traceSegment_082_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1248 17 17, g32p_row03_traceSegment_082_1248_0017, g32p_row03_traceSegment_082_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1215 33 34, g32p_row03_traceSegment_082_1215_0033, g32p_row03_traceSegment_082_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1282 8 9, g32p_row03_traceSegment_082_1282_0008, g32p_row03_traceSegment_082_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1299 8 9, g32p_row03_traceSegment_082_1299_0008, g32p_row03_traceSegment_082_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1282 17 17, g32p_row03_traceSegment_082_1282_0017, g32p_row03_traceSegment_082_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1316 8 9, g32p_row03_traceSegment_082_1316_0008, g32p_row03_traceSegment_082_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1333 8 9, g32p_row03_traceSegment_082_1333_0008, g32p_row03_traceSegment_082_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1316 17 17, g32p_row03_traceSegment_082_1316_0017, g32p_row03_traceSegment_082_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1282 34 34, g32p_row03_traceSegment_082_1282_0034, g32p_row03_traceSegment_082_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1215 67 68, g32p_row03_traceSegment_082_1215_0067, g32p_row03_traceSegment_082_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1080 135 135, g32p_row03_traceSegment_082_1080_0135, g32p_row03_traceSegment_082_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1366 8 9, g32p_row03_traceSegment_082_1366_0008, g32p_row03_traceSegment_082_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1350 16 17, g32p_row03_traceSegment_082_1350_0016, g32p_row03_traceSegment_082_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1383 8 9, g32p_row03_traceSegment_082_1383_0008, g32p_row03_traceSegment_082_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1400 8 9, g32p_row03_traceSegment_082_1400_0008, g32p_row03_traceSegment_082_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1383 17 17, g32p_row03_traceSegment_082_1383_0017, g32p_row03_traceSegment_082_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1350 33 34, g32p_row03_traceSegment_082_1350_0033, g32p_row03_traceSegment_082_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1417 8 9, g32p_row03_traceSegment_082_1417_0008, g32p_row03_traceSegment_082_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1434 8 9, g32p_row03_traceSegment_082_1434_0008, g32p_row03_traceSegment_082_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1417 17 17, g32p_row03_traceSegment_082_1417_0017, g32p_row03_traceSegment_082_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1451 8 9, g32p_row03_traceSegment_082_1451_0008, g32p_row03_traceSegment_082_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1468 8 9, g32p_row03_traceSegment_082_1468_0008, g32p_row03_traceSegment_082_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1451 17 17, g32p_row03_traceSegment_082_1451_0017, g32p_row03_traceSegment_082_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1417 34 34, g32p_row03_traceSegment_082_1417_0034, g32p_row03_traceSegment_082_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1350 67 68, g32p_row03_traceSegment_082_1350_0067, g32p_row03_traceSegment_082_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1501 8 9, g32p_row03_traceSegment_082_1501_0008, g32p_row03_traceSegment_082_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1485 16 17, g32p_row03_traceSegment_082_1485_0016, g32p_row03_traceSegment_082_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1518 8 9, g32p_row03_traceSegment_082_1518_0008, g32p_row03_traceSegment_082_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1535 8 9, g32p_row03_traceSegment_082_1535_0008, g32p_row03_traceSegment_082_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1518 17 17, g32p_row03_traceSegment_082_1518_0017, g32p_row03_traceSegment_082_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1485 33 34, g32p_row03_traceSegment_082_1485_0033, g32p_row03_traceSegment_082_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1552 8 9, g32p_row03_traceSegment_082_1552_0008, g32p_row03_traceSegment_082_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1569 8 9, g32p_row03_traceSegment_082_1569_0008, g32p_row03_traceSegment_082_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1552 17 17, g32p_row03_traceSegment_082_1552_0017, g32p_row03_traceSegment_082_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1586 8 9, g32p_row03_traceSegment_082_1586_0008, g32p_row03_traceSegment_082_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1603 8 9, g32p_row03_traceSegment_082_1603_0008, g32p_row03_traceSegment_082_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1586 17 17, g32p_row03_traceSegment_082_1586_0017, g32p_row03_traceSegment_082_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1552 34 34, g32p_row03_traceSegment_082_1552_0034, g32p_row03_traceSegment_082_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1485 67 68, g32p_row03_traceSegment_082_1485_0067, g32p_row03_traceSegment_082_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1350 135 135, g32p_row03_traceSegment_082_1350_0135, g32p_row03_traceSegment_082_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_082 1080 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1080 270 270, g32p_row03_traceSegment_082_1080_0270, g32p_row03_traceSegment_082_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1636 8 9, g32p_row03_traceSegment_082_1636_0008, g32p_row03_traceSegment_082_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1620 16 17, g32p_row03_traceSegment_082_1620_0016, g32p_row03_traceSegment_082_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1653 8 9, g32p_row03_traceSegment_082_1653_0008, g32p_row03_traceSegment_082_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1670 8 9, g32p_row03_traceSegment_082_1670_0008, g32p_row03_traceSegment_082_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1653 17 17, g32p_row03_traceSegment_082_1653_0017, g32p_row03_traceSegment_082_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1620 33 34, g32p_row03_traceSegment_082_1620_0033, g32p_row03_traceSegment_082_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1687 8 9, g32p_row03_traceSegment_082_1687_0008, g32p_row03_traceSegment_082_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1704 8 9, g32p_row03_traceSegment_082_1704_0008, g32p_row03_traceSegment_082_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1687 17 17, g32p_row03_traceSegment_082_1687_0017, g32p_row03_traceSegment_082_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1721 8 9, g32p_row03_traceSegment_082_1721_0008, g32p_row03_traceSegment_082_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1738 8 9, g32p_row03_traceSegment_082_1738_0008, g32p_row03_traceSegment_082_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1721 17 17, g32p_row03_traceSegment_082_1721_0017, g32p_row03_traceSegment_082_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1687 34 34, g32p_row03_traceSegment_082_1687_0034, g32p_row03_traceSegment_082_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1620 67 68, g32p_row03_traceSegment_082_1620_0067, g32p_row03_traceSegment_082_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1771 8 9, g32p_row03_traceSegment_082_1771_0008, g32p_row03_traceSegment_082_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1755 16 17, g32p_row03_traceSegment_082_1755_0016, g32p_row03_traceSegment_082_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1788 8 9, g32p_row03_traceSegment_082_1788_0008, g32p_row03_traceSegment_082_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1805 8 9, g32p_row03_traceSegment_082_1805_0008, g32p_row03_traceSegment_082_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1788 17 17, g32p_row03_traceSegment_082_1788_0017, g32p_row03_traceSegment_082_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1755 33 34, g32p_row03_traceSegment_082_1755_0033, g32p_row03_traceSegment_082_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1822 8 9, g32p_row03_traceSegment_082_1822_0008, g32p_row03_traceSegment_082_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1839 8 9, g32p_row03_traceSegment_082_1839_0008, g32p_row03_traceSegment_082_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1822 17 17, g32p_row03_traceSegment_082_1822_0017, g32p_row03_traceSegment_082_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1856 8 9, g32p_row03_traceSegment_082_1856_0008, g32p_row03_traceSegment_082_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1873 8 9, g32p_row03_traceSegment_082_1873_0008, g32p_row03_traceSegment_082_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1856 17 17, g32p_row03_traceSegment_082_1856_0017, g32p_row03_traceSegment_082_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1822 34 34, g32p_row03_traceSegment_082_1822_0034, g32p_row03_traceSegment_082_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1755 67 68, g32p_row03_traceSegment_082_1755_0067, g32p_row03_traceSegment_082_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1620 135 135, g32p_row03_traceSegment_082_1620_0135, g32p_row03_traceSegment_082_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1906 8 9, g32p_row03_traceSegment_082_1906_0008, g32p_row03_traceSegment_082_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1890 16 17, g32p_row03_traceSegment_082_1890_0016, g32p_row03_traceSegment_082_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1923 8 9, g32p_row03_traceSegment_082_1923_0008, g32p_row03_traceSegment_082_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1940 8 9, g32p_row03_traceSegment_082_1940_0008, g32p_row03_traceSegment_082_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1923 17 17, g32p_row03_traceSegment_082_1923_0017, g32p_row03_traceSegment_082_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1890 33 34, g32p_row03_traceSegment_082_1890_0033, g32p_row03_traceSegment_082_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1957 8 9, g32p_row03_traceSegment_082_1957_0008, g32p_row03_traceSegment_082_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1974 8 9, g32p_row03_traceSegment_082_1974_0008, g32p_row03_traceSegment_082_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1957 17 17, g32p_row03_traceSegment_082_1957_0017, g32p_row03_traceSegment_082_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1991 8 9, g32p_row03_traceSegment_082_1991_0008, g32p_row03_traceSegment_082_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2008 8 9, g32p_row03_traceSegment_082_2008_0008, g32p_row03_traceSegment_082_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1991 17 17, g32p_row03_traceSegment_082_1991_0017, g32p_row03_traceSegment_082_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1957 34 34, g32p_row03_traceSegment_082_1957_0034, g32p_row03_traceSegment_082_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1890 67 68, g32p_row03_traceSegment_082_1890_0067, g32p_row03_traceSegment_082_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2041 8 9, g32p_row03_traceSegment_082_2041_0008, g32p_row03_traceSegment_082_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2025 16 17, g32p_row03_traceSegment_082_2025_0016, g32p_row03_traceSegment_082_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2058 8 9, g32p_row03_traceSegment_082_2058_0008, g32p_row03_traceSegment_082_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2075 8 9, g32p_row03_traceSegment_082_2075_0008, g32p_row03_traceSegment_082_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2058 17 17, g32p_row03_traceSegment_082_2058_0017, g32p_row03_traceSegment_082_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2025 33 34, g32p_row03_traceSegment_082_2025_0033, g32p_row03_traceSegment_082_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2092 8 9, g32p_row03_traceSegment_082_2092_0008, g32p_row03_traceSegment_082_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2109 8 9, g32p_row03_traceSegment_082_2109_0008, g32p_row03_traceSegment_082_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2092 17 17, g32p_row03_traceSegment_082_2092_0017, g32p_row03_traceSegment_082_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2126 8 9, g32p_row03_traceSegment_082_2126_0008, g32p_row03_traceSegment_082_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2143 8 9, g32p_row03_traceSegment_082_2143_0008, g32p_row03_traceSegment_082_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2126 17 17, g32p_row03_traceSegment_082_2126_0017, g32p_row03_traceSegment_082_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2092 34 34, g32p_row03_traceSegment_082_2092_0034, g32p_row03_traceSegment_082_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2025 67 68, g32p_row03_traceSegment_082_2025_0067, g32p_row03_traceSegment_082_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 1890 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1890 135 135, g32p_row03_traceSegment_082_1890_0135, g32p_row03_traceSegment_082_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_082 1620 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1620 270 270, g32p_row03_traceSegment_082_1620_0270, g32p_row03_traceSegment_082_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_082_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_082 1080 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 1080 540 540, g32p_row03_traceSegment_082_1080_0540, g32p_row03_traceSegment_082_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_082 0 2160 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 0 1080 1080, g32p_row03_traceSegment_082_0000_1080, g32p_row03_traceSegment_082_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2176 8 9, g32p_row03_traceSegment_082_2176_0008, g32p_row03_traceSegment_082_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2160 16 17, g32p_row03_traceSegment_082_2160_0016, g32p_row03_traceSegment_082_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2193 8 9, g32p_row03_traceSegment_082_2193_0008, g32p_row03_traceSegment_082_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2210 8 9, g32p_row03_traceSegment_082_2210_0008, g32p_row03_traceSegment_082_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2193 17 17, g32p_row03_traceSegment_082_2193_0017, g32p_row03_traceSegment_082_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2160 33 34, g32p_row03_traceSegment_082_2160_0033, g32p_row03_traceSegment_082_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2227 8 9, g32p_row03_traceSegment_082_2227_0008, g32p_row03_traceSegment_082_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2244 8 9, g32p_row03_traceSegment_082_2244_0008, g32p_row03_traceSegment_082_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2227 17 17, g32p_row03_traceSegment_082_2227_0017, g32p_row03_traceSegment_082_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2261 8 9, g32p_row03_traceSegment_082_2261_0008, g32p_row03_traceSegment_082_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2278 8 9, g32p_row03_traceSegment_082_2278_0008, g32p_row03_traceSegment_082_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2261 17 17, g32p_row03_traceSegment_082_2261_0017, g32p_row03_traceSegment_082_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2227 34 34, g32p_row03_traceSegment_082_2227_0034, g32p_row03_traceSegment_082_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2160 67 68, g32p_row03_traceSegment_082_2160_0067, g32p_row03_traceSegment_082_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2311 8 9, g32p_row03_traceSegment_082_2311_0008, g32p_row03_traceSegment_082_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2295 16 17, g32p_row03_traceSegment_082_2295_0016, g32p_row03_traceSegment_082_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2328 8 9, g32p_row03_traceSegment_082_2328_0008, g32p_row03_traceSegment_082_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2345 8 9, g32p_row03_traceSegment_082_2345_0008, g32p_row03_traceSegment_082_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2328 17 17, g32p_row03_traceSegment_082_2328_0017, g32p_row03_traceSegment_082_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2295 33 34, g32p_row03_traceSegment_082_2295_0033, g32p_row03_traceSegment_082_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2362 8 9, g32p_row03_traceSegment_082_2362_0008, g32p_row03_traceSegment_082_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2379 8 9, g32p_row03_traceSegment_082_2379_0008, g32p_row03_traceSegment_082_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2362 17 17, g32p_row03_traceSegment_082_2362_0017, g32p_row03_traceSegment_082_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2396 8 9, g32p_row03_traceSegment_082_2396_0008, g32p_row03_traceSegment_082_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2413 8 9, g32p_row03_traceSegment_082_2413_0008, g32p_row03_traceSegment_082_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2396 17 17, g32p_row03_traceSegment_082_2396_0017, g32p_row03_traceSegment_082_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2362 34 34, g32p_row03_traceSegment_082_2362_0034, g32p_row03_traceSegment_082_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2295 67 68, g32p_row03_traceSegment_082_2295_0067, g32p_row03_traceSegment_082_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 2160 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2160 135 135, g32p_row03_traceSegment_082_2160_0135, g32p_row03_traceSegment_082_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2446 8 9, g32p_row03_traceSegment_082_2446_0008, g32p_row03_traceSegment_082_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2430 16 17, g32p_row03_traceSegment_082_2430_0016, g32p_row03_traceSegment_082_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2463 8 9, g32p_row03_traceSegment_082_2463_0008, g32p_row03_traceSegment_082_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2480 8 9, g32p_row03_traceSegment_082_2480_0008, g32p_row03_traceSegment_082_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2463 17 17, g32p_row03_traceSegment_082_2463_0017, g32p_row03_traceSegment_082_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2430 33 34, g32p_row03_traceSegment_082_2430_0033, g32p_row03_traceSegment_082_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2497 8 9, g32p_row03_traceSegment_082_2497_0008, g32p_row03_traceSegment_082_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2514 8 9, g32p_row03_traceSegment_082_2514_0008, g32p_row03_traceSegment_082_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2497 17 17, g32p_row03_traceSegment_082_2497_0017, g32p_row03_traceSegment_082_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2531 8 9, g32p_row03_traceSegment_082_2531_0008, g32p_row03_traceSegment_082_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2548 8 9, g32p_row03_traceSegment_082_2548_0008, g32p_row03_traceSegment_082_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2531 17 17, g32p_row03_traceSegment_082_2531_0017, g32p_row03_traceSegment_082_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2497 34 34, g32p_row03_traceSegment_082_2497_0034, g32p_row03_traceSegment_082_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2430 67 68, g32p_row03_traceSegment_082_2430_0067, g32p_row03_traceSegment_082_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2581 8 9, g32p_row03_traceSegment_082_2581_0008, g32p_row03_traceSegment_082_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2565 16 17, g32p_row03_traceSegment_082_2565_0016, g32p_row03_traceSegment_082_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2598 8 9, g32p_row03_traceSegment_082_2598_0008, g32p_row03_traceSegment_082_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2615 8 9, g32p_row03_traceSegment_082_2615_0008, g32p_row03_traceSegment_082_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2598 17 17, g32p_row03_traceSegment_082_2598_0017, g32p_row03_traceSegment_082_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2565 33 34, g32p_row03_traceSegment_082_2565_0033, g32p_row03_traceSegment_082_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2632 8 9, g32p_row03_traceSegment_082_2632_0008, g32p_row03_traceSegment_082_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2649 8 9, g32p_row03_traceSegment_082_2649_0008, g32p_row03_traceSegment_082_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2632 17 17, g32p_row03_traceSegment_082_2632_0017, g32p_row03_traceSegment_082_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2666 8 9, g32p_row03_traceSegment_082_2666_0008, g32p_row03_traceSegment_082_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2683 8 9, g32p_row03_traceSegment_082_2683_0008, g32p_row03_traceSegment_082_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2666 17 17, g32p_row03_traceSegment_082_2666_0017, g32p_row03_traceSegment_082_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2632 34 34, g32p_row03_traceSegment_082_2632_0034, g32p_row03_traceSegment_082_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2565 67 68, g32p_row03_traceSegment_082_2565_0067, g32p_row03_traceSegment_082_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2430 135 135, g32p_row03_traceSegment_082_2430_0135, g32p_row03_traceSegment_082_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_082 2160 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2160 270 270, g32p_row03_traceSegment_082_2160_0270, g32p_row03_traceSegment_082_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2716 8 9, g32p_row03_traceSegment_082_2716_0008, g32p_row03_traceSegment_082_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2700 16 17, g32p_row03_traceSegment_082_2700_0016, g32p_row03_traceSegment_082_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2733 8 9, g32p_row03_traceSegment_082_2733_0008, g32p_row03_traceSegment_082_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2750 8 9, g32p_row03_traceSegment_082_2750_0008, g32p_row03_traceSegment_082_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2733 17 17, g32p_row03_traceSegment_082_2733_0017, g32p_row03_traceSegment_082_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2700 33 34, g32p_row03_traceSegment_082_2700_0033, g32p_row03_traceSegment_082_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2767 8 9, g32p_row03_traceSegment_082_2767_0008, g32p_row03_traceSegment_082_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2784 8 9, g32p_row03_traceSegment_082_2784_0008, g32p_row03_traceSegment_082_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2767 17 17, g32p_row03_traceSegment_082_2767_0017, g32p_row03_traceSegment_082_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2801 8 9, g32p_row03_traceSegment_082_2801_0008, g32p_row03_traceSegment_082_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2818 8 9, g32p_row03_traceSegment_082_2818_0008, g32p_row03_traceSegment_082_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2801 17 17, g32p_row03_traceSegment_082_2801_0017, g32p_row03_traceSegment_082_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2767 34 34, g32p_row03_traceSegment_082_2767_0034, g32p_row03_traceSegment_082_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2700 67 68, g32p_row03_traceSegment_082_2700_0067, g32p_row03_traceSegment_082_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2851 8 9, g32p_row03_traceSegment_082_2851_0008, g32p_row03_traceSegment_082_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2835 16 17, g32p_row03_traceSegment_082_2835_0016, g32p_row03_traceSegment_082_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2868 8 9, g32p_row03_traceSegment_082_2868_0008, g32p_row03_traceSegment_082_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2885 8 9, g32p_row03_traceSegment_082_2885_0008, g32p_row03_traceSegment_082_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2868 17 17, g32p_row03_traceSegment_082_2868_0017, g32p_row03_traceSegment_082_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2835 33 34, g32p_row03_traceSegment_082_2835_0033, g32p_row03_traceSegment_082_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2902 8 9, g32p_row03_traceSegment_082_2902_0008, g32p_row03_traceSegment_082_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2919 8 9, g32p_row03_traceSegment_082_2919_0008, g32p_row03_traceSegment_082_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2902 17 17, g32p_row03_traceSegment_082_2902_0017, g32p_row03_traceSegment_082_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2936 8 9, g32p_row03_traceSegment_082_2936_0008, g32p_row03_traceSegment_082_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2953 8 9, g32p_row03_traceSegment_082_2953_0008, g32p_row03_traceSegment_082_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2936 17 17, g32p_row03_traceSegment_082_2936_0017, g32p_row03_traceSegment_082_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2902 34 34, g32p_row03_traceSegment_082_2902_0034, g32p_row03_traceSegment_082_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2835 67 68, g32p_row03_traceSegment_082_2835_0067, g32p_row03_traceSegment_082_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2700 135 135, g32p_row03_traceSegment_082_2700_0135, g32p_row03_traceSegment_082_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2986 8 9, g32p_row03_traceSegment_082_2986_0008, g32p_row03_traceSegment_082_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2970 16 17, g32p_row03_traceSegment_082_2970_0016, g32p_row03_traceSegment_082_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3003 8 9, g32p_row03_traceSegment_082_3003_0008, g32p_row03_traceSegment_082_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3020 8 9, g32p_row03_traceSegment_082_3020_0008, g32p_row03_traceSegment_082_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3003 17 17, g32p_row03_traceSegment_082_3003_0017, g32p_row03_traceSegment_082_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2970 33 34, g32p_row03_traceSegment_082_2970_0033, g32p_row03_traceSegment_082_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3037 8 9, g32p_row03_traceSegment_082_3037_0008, g32p_row03_traceSegment_082_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3054 8 9, g32p_row03_traceSegment_082_3054_0008, g32p_row03_traceSegment_082_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3037 17 17, g32p_row03_traceSegment_082_3037_0017, g32p_row03_traceSegment_082_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3071 8 9, g32p_row03_traceSegment_082_3071_0008, g32p_row03_traceSegment_082_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3088 8 9, g32p_row03_traceSegment_082_3088_0008, g32p_row03_traceSegment_082_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3071 17 17, g32p_row03_traceSegment_082_3071_0017, g32p_row03_traceSegment_082_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3037 34 34, g32p_row03_traceSegment_082_3037_0034, g32p_row03_traceSegment_082_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2970 67 68, g32p_row03_traceSegment_082_2970_0067, g32p_row03_traceSegment_082_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3121 8 9, g32p_row03_traceSegment_082_3121_0008, g32p_row03_traceSegment_082_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3105 16 17, g32p_row03_traceSegment_082_3105_0016, g32p_row03_traceSegment_082_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3138 8 9, g32p_row03_traceSegment_082_3138_0008, g32p_row03_traceSegment_082_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3155 8 9, g32p_row03_traceSegment_082_3155_0008, g32p_row03_traceSegment_082_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3138 17 17, g32p_row03_traceSegment_082_3138_0017, g32p_row03_traceSegment_082_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3105 33 34, g32p_row03_traceSegment_082_3105_0033, g32p_row03_traceSegment_082_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3172 8 9, g32p_row03_traceSegment_082_3172_0008, g32p_row03_traceSegment_082_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3189 8 9, g32p_row03_traceSegment_082_3189_0008, g32p_row03_traceSegment_082_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3172 17 17, g32p_row03_traceSegment_082_3172_0017, g32p_row03_traceSegment_082_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3206 8 9, g32p_row03_traceSegment_082_3206_0008, g32p_row03_traceSegment_082_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3223 8 9, g32p_row03_traceSegment_082_3223_0008, g32p_row03_traceSegment_082_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3206 17 17, g32p_row03_traceSegment_082_3206_0017, g32p_row03_traceSegment_082_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3172 34 34, g32p_row03_traceSegment_082_3172_0034, g32p_row03_traceSegment_082_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3105 67 68, g32p_row03_traceSegment_082_3105_0067, g32p_row03_traceSegment_082_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2970 135 135, g32p_row03_traceSegment_082_2970_0135, g32p_row03_traceSegment_082_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_082 2700 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2700 270 270, g32p_row03_traceSegment_082_2700_0270, g32p_row03_traceSegment_082_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_082 2160 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2160 540 540, g32p_row03_traceSegment_082_2160_0540, g32p_row03_traceSegment_082_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3256 8 9, g32p_row03_traceSegment_082_3256_0008, g32p_row03_traceSegment_082_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3240 16 17, g32p_row03_traceSegment_082_3240_0016, g32p_row03_traceSegment_082_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3273 8 9, g32p_row03_traceSegment_082_3273_0008, g32p_row03_traceSegment_082_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3290 8 9, g32p_row03_traceSegment_082_3290_0008, g32p_row03_traceSegment_082_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3273 17 17, g32p_row03_traceSegment_082_3273_0017, g32p_row03_traceSegment_082_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3240 33 34, g32p_row03_traceSegment_082_3240_0033, g32p_row03_traceSegment_082_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3307 8 9, g32p_row03_traceSegment_082_3307_0008, g32p_row03_traceSegment_082_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3324 8 9, g32p_row03_traceSegment_082_3324_0008, g32p_row03_traceSegment_082_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3307 17 17, g32p_row03_traceSegment_082_3307_0017, g32p_row03_traceSegment_082_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3341 8 9, g32p_row03_traceSegment_082_3341_0008, g32p_row03_traceSegment_082_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3358 8 9, g32p_row03_traceSegment_082_3358_0008, g32p_row03_traceSegment_082_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3341 17 17, g32p_row03_traceSegment_082_3341_0017, g32p_row03_traceSegment_082_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3307 34 34, g32p_row03_traceSegment_082_3307_0034, g32p_row03_traceSegment_082_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3240 67 68, g32p_row03_traceSegment_082_3240_0067, g32p_row03_traceSegment_082_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3391 8 9, g32p_row03_traceSegment_082_3391_0008, g32p_row03_traceSegment_082_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3375 16 17, g32p_row03_traceSegment_082_3375_0016, g32p_row03_traceSegment_082_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3408 8 9, g32p_row03_traceSegment_082_3408_0008, g32p_row03_traceSegment_082_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3425 8 9, g32p_row03_traceSegment_082_3425_0008, g32p_row03_traceSegment_082_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3408 17 17, g32p_row03_traceSegment_082_3408_0017, g32p_row03_traceSegment_082_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3375 33 34, g32p_row03_traceSegment_082_3375_0033, g32p_row03_traceSegment_082_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3442 8 9, g32p_row03_traceSegment_082_3442_0008, g32p_row03_traceSegment_082_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3459 8 9, g32p_row03_traceSegment_082_3459_0008, g32p_row03_traceSegment_082_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3442 17 17, g32p_row03_traceSegment_082_3442_0017, g32p_row03_traceSegment_082_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3476 8 9, g32p_row03_traceSegment_082_3476_0008, g32p_row03_traceSegment_082_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3493 8 9, g32p_row03_traceSegment_082_3493_0008, g32p_row03_traceSegment_082_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3476 17 17, g32p_row03_traceSegment_082_3476_0017, g32p_row03_traceSegment_082_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3442 34 34, g32p_row03_traceSegment_082_3442_0034, g32p_row03_traceSegment_082_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3375 67 68, g32p_row03_traceSegment_082_3375_0067, g32p_row03_traceSegment_082_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3240 135 135, g32p_row03_traceSegment_082_3240_0135, g32p_row03_traceSegment_082_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3526 8 9, g32p_row03_traceSegment_082_3526_0008, g32p_row03_traceSegment_082_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3510 16 17, g32p_row03_traceSegment_082_3510_0016, g32p_row03_traceSegment_082_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3543 8 9, g32p_row03_traceSegment_082_3543_0008, g32p_row03_traceSegment_082_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3560 8 9, g32p_row03_traceSegment_082_3560_0008, g32p_row03_traceSegment_082_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3543 17 17, g32p_row03_traceSegment_082_3543_0017, g32p_row03_traceSegment_082_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3510 33 34, g32p_row03_traceSegment_082_3510_0033, g32p_row03_traceSegment_082_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3577 8 9, g32p_row03_traceSegment_082_3577_0008, g32p_row03_traceSegment_082_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3594 8 9, g32p_row03_traceSegment_082_3594_0008, g32p_row03_traceSegment_082_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3577 17 17, g32p_row03_traceSegment_082_3577_0017, g32p_row03_traceSegment_082_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3611 8 9, g32p_row03_traceSegment_082_3611_0008, g32p_row03_traceSegment_082_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3628 8 9, g32p_row03_traceSegment_082_3628_0008, g32p_row03_traceSegment_082_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3611 17 17, g32p_row03_traceSegment_082_3611_0017, g32p_row03_traceSegment_082_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3577 34 34, g32p_row03_traceSegment_082_3577_0034, g32p_row03_traceSegment_082_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3510 67 68, g32p_row03_traceSegment_082_3510_0067, g32p_row03_traceSegment_082_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3661 8 9, g32p_row03_traceSegment_082_3661_0008, g32p_row03_traceSegment_082_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3645 16 17, g32p_row03_traceSegment_082_3645_0016, g32p_row03_traceSegment_082_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3678 8 9, g32p_row03_traceSegment_082_3678_0008, g32p_row03_traceSegment_082_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3695 8 9, g32p_row03_traceSegment_082_3695_0008, g32p_row03_traceSegment_082_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3678 17 17, g32p_row03_traceSegment_082_3678_0017, g32p_row03_traceSegment_082_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3645 33 34, g32p_row03_traceSegment_082_3645_0033, g32p_row03_traceSegment_082_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3712 8 9, g32p_row03_traceSegment_082_3712_0008, g32p_row03_traceSegment_082_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3729 8 9, g32p_row03_traceSegment_082_3729_0008, g32p_row03_traceSegment_082_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3712 17 17, g32p_row03_traceSegment_082_3712_0017, g32p_row03_traceSegment_082_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3746 8 9, g32p_row03_traceSegment_082_3746_0008, g32p_row03_traceSegment_082_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3763 8 9, g32p_row03_traceSegment_082_3763_0008, g32p_row03_traceSegment_082_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3746 17 17, g32p_row03_traceSegment_082_3746_0017, g32p_row03_traceSegment_082_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3712 34 34, g32p_row03_traceSegment_082_3712_0034, g32p_row03_traceSegment_082_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3645 67 68, g32p_row03_traceSegment_082_3645_0067, g32p_row03_traceSegment_082_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 3510 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3510 135 135, g32p_row03_traceSegment_082_3510_0135, g32p_row03_traceSegment_082_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_082 3240 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3240 270 270, g32p_row03_traceSegment_082_3240_0270, g32p_row03_traceSegment_082_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3804 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3796 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3796 8 9, g32p_row03_traceSegment_082_3796_0008, g32p_row03_traceSegment_082_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 3780 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3780 16 17, g32p_row03_traceSegment_082_3780_0016, g32p_row03_traceSegment_082_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3821 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3813 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3813 8 9, g32p_row03_traceSegment_082_3813_0008, g32p_row03_traceSegment_082_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3830 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3838 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3830 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3830 8 9, g32p_row03_traceSegment_082_3830_0008, g32p_row03_traceSegment_082_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3813 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3813 17 17, g32p_row03_traceSegment_082_3813_0017, g32p_row03_traceSegment_082_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 3780 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3780 33 34, g32p_row03_traceSegment_082_3780_0033, g32p_row03_traceSegment_082_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3847 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3847 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3847 8 9, g32p_row03_traceSegment_082_3847_0008, g32p_row03_traceSegment_082_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3872 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3864 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3864 8 9, g32p_row03_traceSegment_082_3864_0008, g32p_row03_traceSegment_082_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3847 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3847 17 17, g32p_row03_traceSegment_082_3847_0017, g32p_row03_traceSegment_082_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3881 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3889 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3881 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3881 8 9, g32p_row03_traceSegment_082_3881_0008, g32p_row03_traceSegment_082_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3898 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3906 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3898 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3898 8 9, g32p_row03_traceSegment_082_3898_0008, g32p_row03_traceSegment_082_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3881 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3881 17 17, g32p_row03_traceSegment_082_3881_0017, g32p_row03_traceSegment_082_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 3847 68 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3847 34 34, g32p_row03_traceSegment_082_3847_0034, g32p_row03_traceSegment_082_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 3780 135 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3780 67 68, g32p_row03_traceSegment_082_3780_0067, g32p_row03_traceSegment_082_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 3915 16 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3931 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3931 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3931 8 9, g32p_row03_traceSegment_082_3931_0008, g32p_row03_traceSegment_082_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 3915 33 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3915 16 17, g32p_row03_traceSegment_082_3915_0016, g32p_row03_traceSegment_082_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3948 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3956 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3948 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3948 8 9, g32p_row03_traceSegment_082_3948_0008, g32p_row03_traceSegment_082_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3965 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3965 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3965 8 9, g32p_row03_traceSegment_082_3965_0008, g32p_row03_traceSegment_082_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3948 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3948 17 17, g32p_row03_traceSegment_082_3948_0017, g32p_row03_traceSegment_082_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 3915 67 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3915 33 34, g32p_row03_traceSegment_082_3915_0033, g32p_row03_traceSegment_082_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3982 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 3990 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3982 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3982 8 9, g32p_row03_traceSegment_082_3982_0008, g32p_row03_traceSegment_082_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4007 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 3999 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3999 8 9, g32p_row03_traceSegment_082_3999_0008, g32p_row03_traceSegment_082_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 3982 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3982 17 17, g32p_row03_traceSegment_082_3982_0017, g32p_row03_traceSegment_082_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4016 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4016 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4016 8 9, g32p_row03_traceSegment_082_4016_0008, g32p_row03_traceSegment_082_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4033 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4041 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4033 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4033 8 9, g32p_row03_traceSegment_082_4033_0008, g32p_row03_traceSegment_082_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 4016 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4016 17 17, g32p_row03_traceSegment_082_4016_0017, g32p_row03_traceSegment_082_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 3982 68 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3982 34 34, g32p_row03_traceSegment_082_3982_0034, g32p_row03_traceSegment_082_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 3915 135 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3915 67 68, g32p_row03_traceSegment_082_3915_0067, g32p_row03_traceSegment_082_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 3780 270 = [0, 0, 0, 0, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3780 135 135, g32p_row03_traceSegment_082_3780_0135, g32p_row03_traceSegment_082_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4074 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4066 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4066 8 9, g32p_row03_traceSegment_082_4066_0008, g32p_row03_traceSegment_082_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 4050 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4050 16 17, g32p_row03_traceSegment_082_4050_0016, g32p_row03_traceSegment_082_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4083 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4091 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4083 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4083 8 9, g32p_row03_traceSegment_082_4083_0008, g32p_row03_traceSegment_082_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4100 8 9, g32p_row03_traceSegment_082_4100_0008, g32p_row03_traceSegment_082_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 4083 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4083 17 17, g32p_row03_traceSegment_082_4083_0017, g32p_row03_traceSegment_082_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 4050 67 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4050 33 34, g32p_row03_traceSegment_082_4050_0033, g32p_row03_traceSegment_082_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4117 8 9, g32p_row03_traceSegment_082_4117_0008, g32p_row03_traceSegment_082_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4134 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4134 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4134 8 9, g32p_row03_traceSegment_082_4134_0008, g32p_row03_traceSegment_082_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 4117 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4117 17 17, g32p_row03_traceSegment_082_4117_0017, g32p_row03_traceSegment_082_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4151 8 9, g32p_row03_traceSegment_082_4151_0008, g32p_row03_traceSegment_082_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4168 8 9, g32p_row03_traceSegment_082_4168_0008, g32p_row03_traceSegment_082_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4151 17 17, g32p_row03_traceSegment_082_4151_0017, g32p_row03_traceSegment_082_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 4117 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4117 34 34, g32p_row03_traceSegment_082_4117_0034, g32p_row03_traceSegment_082_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 4050 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4050 67 68, g32p_row03_traceSegment_082_4050_0067, g32p_row03_traceSegment_082_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_082 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4201 8 9, g32p_row03_traceSegment_082_4201_0008, g32p_row03_traceSegment_082_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_082 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4185 16 17, g32p_row03_traceSegment_082_4185_0016, g32p_row03_traceSegment_082_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4218 8 9, g32p_row03_traceSegment_082_4218_0008, g32p_row03_traceSegment_082_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4235 8 9, g32p_row03_traceSegment_082_4235_0008, g32p_row03_traceSegment_082_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4218 17 17, g32p_row03_traceSegment_082_4218_0017, g32p_row03_traceSegment_082_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_082 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4185 33 34, g32p_row03_traceSegment_082_4185_0033, g32p_row03_traceSegment_082_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4252 8 9, g32p_row03_traceSegment_082_4252_0008, g32p_row03_traceSegment_082_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4269 8 9, g32p_row03_traceSegment_082_4269_0008, g32p_row03_traceSegment_082_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4252 17 17, g32p_row03_traceSegment_082_4252_0017, g32p_row03_traceSegment_082_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4286 8 9, g32p_row03_traceSegment_082_4286_0008, g32p_row03_traceSegment_082_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_082 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_082 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_082_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_082 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4303 8 9, g32p_row03_traceSegment_082_4303_0008, g32p_row03_traceSegment_082_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_082 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4286 17 17, g32p_row03_traceSegment_082_4286_0017, g32p_row03_traceSegment_082_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_082 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4252 34 34, g32p_row03_traceSegment_082_4252_0034, g32p_row03_traceSegment_082_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_082 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4185 67 68, g32p_row03_traceSegment_082_4185_0067, g32p_row03_traceSegment_082_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_082_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_082 4050 270 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 4050 135 135, g32p_row03_traceSegment_082_4050_0135, g32p_row03_traceSegment_082_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_082 3780 540 = [0, 0, 0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3780 270 270, g32p_row03_traceSegment_082_3780_0270, g32p_row03_traceSegment_082_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_082_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_082 3240 1080 = [0, 0, 0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 3240 540 540, g32p_row03_traceSegment_082_3240_0540, g32p_row03_traceSegment_082_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_082_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_082 2160 2160 = [0, 0, 0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 2160 1080 1080, g32p_row03_traceSegment_082_2160_1080, g32p_row03_traceSegment_082_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_082_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_082 0 4320 = [0, 0, 0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_082 0 2160 2160, g32p_row03_traceSegment_082_0000_2160, g32p_row03_traceSegment_082_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 82 = [0, 0, 0, 0, 0, 30] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_082_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_084 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 84 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_084_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 16 8 9, g32p_row03_traceSegment_084_0016_0008, g32p_row03_traceSegment_084_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 0 16 17, g32p_row03_traceSegment_084_0000_0016, g32p_row03_traceSegment_084_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 33 8 9, g32p_row03_traceSegment_084_0033_0008, g32p_row03_traceSegment_084_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 50 8 9, g32p_row03_traceSegment_084_0050_0008, g32p_row03_traceSegment_084_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 33 17 17, g32p_row03_traceSegment_084_0033_0017, g32p_row03_traceSegment_084_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 0 33 34, g32p_row03_traceSegment_084_0000_0033, g32p_row03_traceSegment_084_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 75 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 67 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 67 8 9, g32p_row03_traceSegment_084_0067_0008, g32p_row03_traceSegment_084_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 84 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 92 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 84 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 84 8 9, g32p_row03_traceSegment_084_0084_0008, g32p_row03_traceSegment_084_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 67 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 67 17 17, g32p_row03_traceSegment_084_0067_0017, g32p_row03_traceSegment_084_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 101 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 109 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 101 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 101 8 9, g32p_row03_traceSegment_084_0101_0008, g32p_row03_traceSegment_084_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 118 8 9, g32p_row03_traceSegment_084_0118_0008, g32p_row03_traceSegment_084_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 101 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 101 17 17, g32p_row03_traceSegment_084_0101_0017, g32p_row03_traceSegment_084_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 67 68 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 67 34 34, g32p_row03_traceSegment_084_0067_0034, g32p_row03_traceSegment_084_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 0 135 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 0 67 68, g32p_row03_traceSegment_084_0000_0067, g32p_row03_traceSegment_084_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 151 8 9, g32p_row03_traceSegment_084_0151_0008, g32p_row03_traceSegment_084_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 135 16 17, g32p_row03_traceSegment_084_0135_0016, g32p_row03_traceSegment_084_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 168 8 9, g32p_row03_traceSegment_084_0168_0008, g32p_row03_traceSegment_084_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 185 8 9, g32p_row03_traceSegment_084_0185_0008, g32p_row03_traceSegment_084_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 168 17 17, g32p_row03_traceSegment_084_0168_0017, g32p_row03_traceSegment_084_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 135 33 34, g32p_row03_traceSegment_084_0135_0033, g32p_row03_traceSegment_084_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 202 8 9, g32p_row03_traceSegment_084_0202_0008, g32p_row03_traceSegment_084_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 219 8 9, g32p_row03_traceSegment_084_0219_0008, g32p_row03_traceSegment_084_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 202 17 17, g32p_row03_traceSegment_084_0202_0017, g32p_row03_traceSegment_084_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 236 8 9, g32p_row03_traceSegment_084_0236_0008, g32p_row03_traceSegment_084_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 253 8 9, g32p_row03_traceSegment_084_0253_0008, g32p_row03_traceSegment_084_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 236 17 17, g32p_row03_traceSegment_084_0236_0017, g32p_row03_traceSegment_084_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 202 34 34, g32p_row03_traceSegment_084_0202_0034, g32p_row03_traceSegment_084_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 135 67 68, g32p_row03_traceSegment_084_0135_0067, g32p_row03_traceSegment_084_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 0 270 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 0 135 135, g32p_row03_traceSegment_084_0000_0135, g32p_row03_traceSegment_084_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 286 8 9, g32p_row03_traceSegment_084_0286_0008, g32p_row03_traceSegment_084_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 270 16 17, g32p_row03_traceSegment_084_0270_0016, g32p_row03_traceSegment_084_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 303 8 9, g32p_row03_traceSegment_084_0303_0008, g32p_row03_traceSegment_084_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 320 8 9, g32p_row03_traceSegment_084_0320_0008, g32p_row03_traceSegment_084_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 303 17 17, g32p_row03_traceSegment_084_0303_0017, g32p_row03_traceSegment_084_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 270 33 34, g32p_row03_traceSegment_084_0270_0033, g32p_row03_traceSegment_084_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 337 8 9, g32p_row03_traceSegment_084_0337_0008, g32p_row03_traceSegment_084_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 354 8 9, g32p_row03_traceSegment_084_0354_0008, g32p_row03_traceSegment_084_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 337 17 17, g32p_row03_traceSegment_084_0337_0017, g32p_row03_traceSegment_084_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 371 8 9, g32p_row03_traceSegment_084_0371_0008, g32p_row03_traceSegment_084_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 388 8 9, g32p_row03_traceSegment_084_0388_0008, g32p_row03_traceSegment_084_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 371 17 17, g32p_row03_traceSegment_084_0371_0017, g32p_row03_traceSegment_084_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 337 34 34, g32p_row03_traceSegment_084_0337_0034, g32p_row03_traceSegment_084_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 270 67 68, g32p_row03_traceSegment_084_0270_0067, g32p_row03_traceSegment_084_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 421 8 9, g32p_row03_traceSegment_084_0421_0008, g32p_row03_traceSegment_084_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 405 16 17, g32p_row03_traceSegment_084_0405_0016, g32p_row03_traceSegment_084_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 438 8 9, g32p_row03_traceSegment_084_0438_0008, g32p_row03_traceSegment_084_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 455 8 9, g32p_row03_traceSegment_084_0455_0008, g32p_row03_traceSegment_084_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 438 17 17, g32p_row03_traceSegment_084_0438_0017, g32p_row03_traceSegment_084_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 405 33 34, g32p_row03_traceSegment_084_0405_0033, g32p_row03_traceSegment_084_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 472 8 9, g32p_row03_traceSegment_084_0472_0008, g32p_row03_traceSegment_084_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 489 8 9, g32p_row03_traceSegment_084_0489_0008, g32p_row03_traceSegment_084_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 472 17 17, g32p_row03_traceSegment_084_0472_0017, g32p_row03_traceSegment_084_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 506 8 9, g32p_row03_traceSegment_084_0506_0008, g32p_row03_traceSegment_084_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 523 8 9, g32p_row03_traceSegment_084_0523_0008, g32p_row03_traceSegment_084_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 506 17 17, g32p_row03_traceSegment_084_0506_0017, g32p_row03_traceSegment_084_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 472 34 34, g32p_row03_traceSegment_084_0472_0034, g32p_row03_traceSegment_084_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 405 67 68, g32p_row03_traceSegment_084_0405_0067, g32p_row03_traceSegment_084_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 270 135 135, g32p_row03_traceSegment_084_0270_0135, g32p_row03_traceSegment_084_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_084 0 540 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 0 270 270, g32p_row03_traceSegment_084_0000_0270, g32p_row03_traceSegment_084_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 556 8 9, g32p_row03_traceSegment_084_0556_0008, g32p_row03_traceSegment_084_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 540 16 17, g32p_row03_traceSegment_084_0540_0016, g32p_row03_traceSegment_084_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 573 8 9, g32p_row03_traceSegment_084_0573_0008, g32p_row03_traceSegment_084_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 590 8 9, g32p_row03_traceSegment_084_0590_0008, g32p_row03_traceSegment_084_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 573 17 17, g32p_row03_traceSegment_084_0573_0017, g32p_row03_traceSegment_084_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 540 33 34, g32p_row03_traceSegment_084_0540_0033, g32p_row03_traceSegment_084_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 607 8 9, g32p_row03_traceSegment_084_0607_0008, g32p_row03_traceSegment_084_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 624 8 9, g32p_row03_traceSegment_084_0624_0008, g32p_row03_traceSegment_084_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 607 17 17, g32p_row03_traceSegment_084_0607_0017, g32p_row03_traceSegment_084_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 641 8 9, g32p_row03_traceSegment_084_0641_0008, g32p_row03_traceSegment_084_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 658 8 9, g32p_row03_traceSegment_084_0658_0008, g32p_row03_traceSegment_084_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 641 17 17, g32p_row03_traceSegment_084_0641_0017, g32p_row03_traceSegment_084_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 607 34 34, g32p_row03_traceSegment_084_0607_0034, g32p_row03_traceSegment_084_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 540 67 68, g32p_row03_traceSegment_084_0540_0067, g32p_row03_traceSegment_084_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 691 8 9, g32p_row03_traceSegment_084_0691_0008, g32p_row03_traceSegment_084_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 675 16 17, g32p_row03_traceSegment_084_0675_0016, g32p_row03_traceSegment_084_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 708 8 9, g32p_row03_traceSegment_084_0708_0008, g32p_row03_traceSegment_084_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 725 8 9, g32p_row03_traceSegment_084_0725_0008, g32p_row03_traceSegment_084_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 708 17 17, g32p_row03_traceSegment_084_0708_0017, g32p_row03_traceSegment_084_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 675 33 34, g32p_row03_traceSegment_084_0675_0033, g32p_row03_traceSegment_084_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 742 8 9, g32p_row03_traceSegment_084_0742_0008, g32p_row03_traceSegment_084_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 767 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 759 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 759 8 9, g32p_row03_traceSegment_084_0759_0008, g32p_row03_traceSegment_084_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 742 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 742 17 17, g32p_row03_traceSegment_084_0742_0017, g32p_row03_traceSegment_084_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 776 8 9, g32p_row03_traceSegment_084_0776_0008, g32p_row03_traceSegment_084_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 793 8 9, g32p_row03_traceSegment_084_0793_0008, g32p_row03_traceSegment_084_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 776 17 17, g32p_row03_traceSegment_084_0776_0017, g32p_row03_traceSegment_084_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 742 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 742 34 34, g32p_row03_traceSegment_084_0742_0034, g32p_row03_traceSegment_084_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 675 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 675 67 68, g32p_row03_traceSegment_084_0675_0067, g32p_row03_traceSegment_084_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 540 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 540 135 135, g32p_row03_traceSegment_084_0540_0135, g32p_row03_traceSegment_084_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 810 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 826 8 9, g32p_row03_traceSegment_084_0826_0008, g32p_row03_traceSegment_084_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 810 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 810 16 17, g32p_row03_traceSegment_084_0810_0016, g32p_row03_traceSegment_084_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 843 8 9, g32p_row03_traceSegment_084_0843_0008, g32p_row03_traceSegment_084_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 868 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 860 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 860 8 9, g32p_row03_traceSegment_084_0860_0008, g32p_row03_traceSegment_084_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 843 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 843 17 17, g32p_row03_traceSegment_084_0843_0017, g32p_row03_traceSegment_084_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 810 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 810 33 34, g32p_row03_traceSegment_084_0810_0033, g32p_row03_traceSegment_084_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 877 8 9, g32p_row03_traceSegment_084_0877_0008, g32p_row03_traceSegment_084_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 894 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 894 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 894 8 9, g32p_row03_traceSegment_084_0894_0008, g32p_row03_traceSegment_084_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 877 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 877 17 17, g32p_row03_traceSegment_084_0877_0017, g32p_row03_traceSegment_084_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 911 8 9, g32p_row03_traceSegment_084_0911_0008, g32p_row03_traceSegment_084_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 928 8 9, g32p_row03_traceSegment_084_0928_0008, g32p_row03_traceSegment_084_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 911 17 17, g32p_row03_traceSegment_084_0911_0017, g32p_row03_traceSegment_084_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 877 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 877 34 34, g32p_row03_traceSegment_084_0877_0034, g32p_row03_traceSegment_084_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 810 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 810 67 68, g32p_row03_traceSegment_084_0810_0067, g32p_row03_traceSegment_084_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 961 8 9, g32p_row03_traceSegment_084_0961_0008, g32p_row03_traceSegment_084_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 945 16 17, g32p_row03_traceSegment_084_0945_0016, g32p_row03_traceSegment_084_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 986 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 978 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 978 8 9, g32p_row03_traceSegment_084_0978_0008, g32p_row03_traceSegment_084_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 995 8 9, g32p_row03_traceSegment_084_0995_0008, g32p_row03_traceSegment_084_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 978 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 978 17 17, g32p_row03_traceSegment_084_0978_0017, g32p_row03_traceSegment_084_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 945 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 945 33 34, g32p_row03_traceSegment_084_0945_0033, g32p_row03_traceSegment_084_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1012 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1012 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1012 8 9, g32p_row03_traceSegment_084_1012_0008, g32p_row03_traceSegment_084_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1029 8 9, g32p_row03_traceSegment_084_1029_0008, g32p_row03_traceSegment_084_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1012 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1012 17 17, g32p_row03_traceSegment_084_1012_0017, g32p_row03_traceSegment_084_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1046 8 9, g32p_row03_traceSegment_084_1046_0008, g32p_row03_traceSegment_084_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1063 8 9, g32p_row03_traceSegment_084_1063_0008, g32p_row03_traceSegment_084_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1046 17 17, g32p_row03_traceSegment_084_1046_0017, g32p_row03_traceSegment_084_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 1012 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1012 34 34, g32p_row03_traceSegment_084_1012_0034, g32p_row03_traceSegment_084_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 945 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 945 67 68, g32p_row03_traceSegment_084_0945_0067, g32p_row03_traceSegment_084_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 810 270 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 810 135 135, g32p_row03_traceSegment_084_0810_0135, g32p_row03_traceSegment_084_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_084 540 540 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 540 270 270, g32p_row03_traceSegment_084_0540_0270, g32p_row03_traceSegment_084_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_084 0 1080 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 0 540 540, g32p_row03_traceSegment_084_0000_0540, g32p_row03_traceSegment_084_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 1080 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1096 8 9, g32p_row03_traceSegment_084_1096_0008, g32p_row03_traceSegment_084_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 1080 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1080 16 17, g32p_row03_traceSegment_084_1080_0016, g32p_row03_traceSegment_084_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1113 8 9, g32p_row03_traceSegment_084_1113_0008, g32p_row03_traceSegment_084_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1138 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1130 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1130 8 9, g32p_row03_traceSegment_084_1130_0008, g32p_row03_traceSegment_084_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1113 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1113 17 17, g32p_row03_traceSegment_084_1113_0017, g32p_row03_traceSegment_084_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 1080 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1080 33 34, g32p_row03_traceSegment_084_1080_0033, g32p_row03_traceSegment_084_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1147 8 9, g32p_row03_traceSegment_084_1147_0008, g32p_row03_traceSegment_084_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1164 8 9, g32p_row03_traceSegment_084_1164_0008, g32p_row03_traceSegment_084_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1147 17 17, g32p_row03_traceSegment_084_1147_0017, g32p_row03_traceSegment_084_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1181 8 9, g32p_row03_traceSegment_084_1181_0008, g32p_row03_traceSegment_084_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1198 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1198 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1198 8 9, g32p_row03_traceSegment_084_1198_0008, g32p_row03_traceSegment_084_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1181 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1181 17 17, g32p_row03_traceSegment_084_1181_0017, g32p_row03_traceSegment_084_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 1147 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1147 34 34, g32p_row03_traceSegment_084_1147_0034, g32p_row03_traceSegment_084_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 1080 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1080 67 68, g32p_row03_traceSegment_084_1080_0067, g32p_row03_traceSegment_084_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1231 8 9, g32p_row03_traceSegment_084_1231_0008, g32p_row03_traceSegment_084_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1215 16 17, g32p_row03_traceSegment_084_1215_0016, g32p_row03_traceSegment_084_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1248 8 9, g32p_row03_traceSegment_084_1248_0008, g32p_row03_traceSegment_084_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1265 8 9, g32p_row03_traceSegment_084_1265_0008, g32p_row03_traceSegment_084_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1248 17 17, g32p_row03_traceSegment_084_1248_0017, g32p_row03_traceSegment_084_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1215 33 34, g32p_row03_traceSegment_084_1215_0033, g32p_row03_traceSegment_084_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1282 8 9, g32p_row03_traceSegment_084_1282_0008, g32p_row03_traceSegment_084_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1299 8 9, g32p_row03_traceSegment_084_1299_0008, g32p_row03_traceSegment_084_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1282 17 17, g32p_row03_traceSegment_084_1282_0017, g32p_row03_traceSegment_084_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1316 8 9, g32p_row03_traceSegment_084_1316_0008, g32p_row03_traceSegment_084_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1333 8 9, g32p_row03_traceSegment_084_1333_0008, g32p_row03_traceSegment_084_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1316 17 17, g32p_row03_traceSegment_084_1316_0017, g32p_row03_traceSegment_084_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1282 34 34, g32p_row03_traceSegment_084_1282_0034, g32p_row03_traceSegment_084_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1215 67 68, g32p_row03_traceSegment_084_1215_0067, g32p_row03_traceSegment_084_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 1080 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1080 135 135, g32p_row03_traceSegment_084_1080_0135, g32p_row03_traceSegment_084_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1366 8 9, g32p_row03_traceSegment_084_1366_0008, g32p_row03_traceSegment_084_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1350 16 17, g32p_row03_traceSegment_084_1350_0016, g32p_row03_traceSegment_084_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1383 8 9, g32p_row03_traceSegment_084_1383_0008, g32p_row03_traceSegment_084_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1400 8 9, g32p_row03_traceSegment_084_1400_0008, g32p_row03_traceSegment_084_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1383 17 17, g32p_row03_traceSegment_084_1383_0017, g32p_row03_traceSegment_084_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1350 33 34, g32p_row03_traceSegment_084_1350_0033, g32p_row03_traceSegment_084_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1417 8 9, g32p_row03_traceSegment_084_1417_0008, g32p_row03_traceSegment_084_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1434 8 9, g32p_row03_traceSegment_084_1434_0008, g32p_row03_traceSegment_084_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1417 17 17, g32p_row03_traceSegment_084_1417_0017, g32p_row03_traceSegment_084_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1451 8 9, g32p_row03_traceSegment_084_1451_0008, g32p_row03_traceSegment_084_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1468 8 9, g32p_row03_traceSegment_084_1468_0008, g32p_row03_traceSegment_084_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1451 17 17, g32p_row03_traceSegment_084_1451_0017, g32p_row03_traceSegment_084_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1417 34 34, g32p_row03_traceSegment_084_1417_0034, g32p_row03_traceSegment_084_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1350 67 68, g32p_row03_traceSegment_084_1350_0067, g32p_row03_traceSegment_084_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1501 8 9, g32p_row03_traceSegment_084_1501_0008, g32p_row03_traceSegment_084_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1485 16 17, g32p_row03_traceSegment_084_1485_0016, g32p_row03_traceSegment_084_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1518 8 9, g32p_row03_traceSegment_084_1518_0008, g32p_row03_traceSegment_084_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1535 8 9, g32p_row03_traceSegment_084_1535_0008, g32p_row03_traceSegment_084_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1518 17 17, g32p_row03_traceSegment_084_1518_0017, g32p_row03_traceSegment_084_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1485 33 34, g32p_row03_traceSegment_084_1485_0033, g32p_row03_traceSegment_084_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1552 8 9, g32p_row03_traceSegment_084_1552_0008, g32p_row03_traceSegment_084_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1569 8 9, g32p_row03_traceSegment_084_1569_0008, g32p_row03_traceSegment_084_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1552 17 17, g32p_row03_traceSegment_084_1552_0017, g32p_row03_traceSegment_084_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1586 8 9, g32p_row03_traceSegment_084_1586_0008, g32p_row03_traceSegment_084_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1603 8 9, g32p_row03_traceSegment_084_1603_0008, g32p_row03_traceSegment_084_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1586 17 17, g32p_row03_traceSegment_084_1586_0017, g32p_row03_traceSegment_084_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1552 34 34, g32p_row03_traceSegment_084_1552_0034, g32p_row03_traceSegment_084_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1485 67 68, g32p_row03_traceSegment_084_1485_0067, g32p_row03_traceSegment_084_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1350 135 135, g32p_row03_traceSegment_084_1350_0135, g32p_row03_traceSegment_084_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_084 1080 540 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1080 270 270, g32p_row03_traceSegment_084_1080_0270, g32p_row03_traceSegment_084_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1636 8 9, g32p_row03_traceSegment_084_1636_0008, g32p_row03_traceSegment_084_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1620 16 17, g32p_row03_traceSegment_084_1620_0016, g32p_row03_traceSegment_084_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1653 8 9, g32p_row03_traceSegment_084_1653_0008, g32p_row03_traceSegment_084_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1670 8 9, g32p_row03_traceSegment_084_1670_0008, g32p_row03_traceSegment_084_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1653 17 17, g32p_row03_traceSegment_084_1653_0017, g32p_row03_traceSegment_084_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1620 33 34, g32p_row03_traceSegment_084_1620_0033, g32p_row03_traceSegment_084_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1687 8 9, g32p_row03_traceSegment_084_1687_0008, g32p_row03_traceSegment_084_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1704 8 9, g32p_row03_traceSegment_084_1704_0008, g32p_row03_traceSegment_084_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1687 17 17, g32p_row03_traceSegment_084_1687_0017, g32p_row03_traceSegment_084_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1721 8 9, g32p_row03_traceSegment_084_1721_0008, g32p_row03_traceSegment_084_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1738 8 9, g32p_row03_traceSegment_084_1738_0008, g32p_row03_traceSegment_084_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1721 17 17, g32p_row03_traceSegment_084_1721_0017, g32p_row03_traceSegment_084_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1687 34 34, g32p_row03_traceSegment_084_1687_0034, g32p_row03_traceSegment_084_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1620 67 68, g32p_row03_traceSegment_084_1620_0067, g32p_row03_traceSegment_084_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1771 8 9, g32p_row03_traceSegment_084_1771_0008, g32p_row03_traceSegment_084_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1755 16 17, g32p_row03_traceSegment_084_1755_0016, g32p_row03_traceSegment_084_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1788 8 9, g32p_row03_traceSegment_084_1788_0008, g32p_row03_traceSegment_084_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1805 8 9, g32p_row03_traceSegment_084_1805_0008, g32p_row03_traceSegment_084_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1788 17 17, g32p_row03_traceSegment_084_1788_0017, g32p_row03_traceSegment_084_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1755 33 34, g32p_row03_traceSegment_084_1755_0033, g32p_row03_traceSegment_084_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1822 8 9, g32p_row03_traceSegment_084_1822_0008, g32p_row03_traceSegment_084_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1839 8 9, g32p_row03_traceSegment_084_1839_0008, g32p_row03_traceSegment_084_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1822 17 17, g32p_row03_traceSegment_084_1822_0017, g32p_row03_traceSegment_084_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1856 8 9, g32p_row03_traceSegment_084_1856_0008, g32p_row03_traceSegment_084_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1873 8 9, g32p_row03_traceSegment_084_1873_0008, g32p_row03_traceSegment_084_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1856 17 17, g32p_row03_traceSegment_084_1856_0017, g32p_row03_traceSegment_084_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1822 34 34, g32p_row03_traceSegment_084_1822_0034, g32p_row03_traceSegment_084_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1755 67 68, g32p_row03_traceSegment_084_1755_0067, g32p_row03_traceSegment_084_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1620 135 135, g32p_row03_traceSegment_084_1620_0135, g32p_row03_traceSegment_084_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1906 8 9, g32p_row03_traceSegment_084_1906_0008, g32p_row03_traceSegment_084_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1890 16 17, g32p_row03_traceSegment_084_1890_0016, g32p_row03_traceSegment_084_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1923 8 9, g32p_row03_traceSegment_084_1923_0008, g32p_row03_traceSegment_084_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1940 8 9, g32p_row03_traceSegment_084_1940_0008, g32p_row03_traceSegment_084_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1923 17 17, g32p_row03_traceSegment_084_1923_0017, g32p_row03_traceSegment_084_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1890 33 34, g32p_row03_traceSegment_084_1890_0033, g32p_row03_traceSegment_084_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1957 8 9, g32p_row03_traceSegment_084_1957_0008, g32p_row03_traceSegment_084_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1974 8 9, g32p_row03_traceSegment_084_1974_0008, g32p_row03_traceSegment_084_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1957 17 17, g32p_row03_traceSegment_084_1957_0017, g32p_row03_traceSegment_084_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1991 8 9, g32p_row03_traceSegment_084_1991_0008, g32p_row03_traceSegment_084_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2008 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2016 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2008 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2008 8 9, g32p_row03_traceSegment_084_2008_0008, g32p_row03_traceSegment_084_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 1991 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1991 17 17, g32p_row03_traceSegment_084_1991_0017, g32p_row03_traceSegment_084_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 1957 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1957 34 34, g32p_row03_traceSegment_084_1957_0034, g32p_row03_traceSegment_084_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 1890 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1890 67 68, g32p_row03_traceSegment_084_1890_0067, g32p_row03_traceSegment_084_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 2025 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2041 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2041 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2041 8 9, g32p_row03_traceSegment_084_2041_0008, g32p_row03_traceSegment_084_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 2025 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2025 16 17, g32p_row03_traceSegment_084_2025_0016, g32p_row03_traceSegment_084_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2058 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2058 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2058 8 9, g32p_row03_traceSegment_084_2058_0008, g32p_row03_traceSegment_084_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2083 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2075 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2075 8 9, g32p_row03_traceSegment_084_2075_0008, g32p_row03_traceSegment_084_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2058 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2058 17 17, g32p_row03_traceSegment_084_2058_0017, g32p_row03_traceSegment_084_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 2025 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2025 33 34, g32p_row03_traceSegment_084_2025_0033, g32p_row03_traceSegment_084_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2092 8 9, g32p_row03_traceSegment_084_2092_0008, g32p_row03_traceSegment_084_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2109 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2109 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2109 8 9, g32p_row03_traceSegment_084_2109_0008, g32p_row03_traceSegment_084_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2092 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2092 17 17, g32p_row03_traceSegment_084_2092_0017, g32p_row03_traceSegment_084_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2126 8 9, g32p_row03_traceSegment_084_2126_0008, g32p_row03_traceSegment_084_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2143 8 9, g32p_row03_traceSegment_084_2143_0008, g32p_row03_traceSegment_084_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2126 17 17, g32p_row03_traceSegment_084_2126_0017, g32p_row03_traceSegment_084_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 2092 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2092 34 34, g32p_row03_traceSegment_084_2092_0034, g32p_row03_traceSegment_084_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 2025 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2025 67 68, g32p_row03_traceSegment_084_2025_0067, g32p_row03_traceSegment_084_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 1890 270 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1890 135 135, g32p_row03_traceSegment_084_1890_0135, g32p_row03_traceSegment_084_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_084 1620 540 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1620 270 270, g32p_row03_traceSegment_084_1620_0270, g32p_row03_traceSegment_084_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_084_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_084 1080 1080 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 1080 540 540, g32p_row03_traceSegment_084_1080_0540, g32p_row03_traceSegment_084_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_084 0 2160 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 0 1080 1080, g32p_row03_traceSegment_084_0000_1080, g32p_row03_traceSegment_084_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 2160 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2176 8 9, g32p_row03_traceSegment_084_2176_0008, g32p_row03_traceSegment_084_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 2160 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2160 16 17, g32p_row03_traceSegment_084_2160_0016, g32p_row03_traceSegment_084_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2193 8 9, g32p_row03_traceSegment_084_2193_0008, g32p_row03_traceSegment_084_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2210 8 9, g32p_row03_traceSegment_084_2210_0008, g32p_row03_traceSegment_084_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2193 17 17, g32p_row03_traceSegment_084_2193_0017, g32p_row03_traceSegment_084_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 2160 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2160 33 34, g32p_row03_traceSegment_084_2160_0033, g32p_row03_traceSegment_084_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2227 8 9, g32p_row03_traceSegment_084_2227_0008, g32p_row03_traceSegment_084_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2244 8 9, g32p_row03_traceSegment_084_2244_0008, g32p_row03_traceSegment_084_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2227 17 17, g32p_row03_traceSegment_084_2227_0017, g32p_row03_traceSegment_084_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2261 8 9, g32p_row03_traceSegment_084_2261_0008, g32p_row03_traceSegment_084_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2278 8 9, g32p_row03_traceSegment_084_2278_0008, g32p_row03_traceSegment_084_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2261 17 17, g32p_row03_traceSegment_084_2261_0017, g32p_row03_traceSegment_084_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2227 34 34, g32p_row03_traceSegment_084_2227_0034, g32p_row03_traceSegment_084_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 2160 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2160 67 68, g32p_row03_traceSegment_084_2160_0067, g32p_row03_traceSegment_084_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2311 8 9, g32p_row03_traceSegment_084_2311_0008, g32p_row03_traceSegment_084_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2295 16 17, g32p_row03_traceSegment_084_2295_0016, g32p_row03_traceSegment_084_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2328 8 9, g32p_row03_traceSegment_084_2328_0008, g32p_row03_traceSegment_084_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2345 8 9, g32p_row03_traceSegment_084_2345_0008, g32p_row03_traceSegment_084_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2328 17 17, g32p_row03_traceSegment_084_2328_0017, g32p_row03_traceSegment_084_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2295 33 34, g32p_row03_traceSegment_084_2295_0033, g32p_row03_traceSegment_084_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2362 8 9, g32p_row03_traceSegment_084_2362_0008, g32p_row03_traceSegment_084_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2379 8 9, g32p_row03_traceSegment_084_2379_0008, g32p_row03_traceSegment_084_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2362 17 17, g32p_row03_traceSegment_084_2362_0017, g32p_row03_traceSegment_084_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2396 8 9, g32p_row03_traceSegment_084_2396_0008, g32p_row03_traceSegment_084_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2413 8 9, g32p_row03_traceSegment_084_2413_0008, g32p_row03_traceSegment_084_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2396 17 17, g32p_row03_traceSegment_084_2396_0017, g32p_row03_traceSegment_084_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2362 34 34, g32p_row03_traceSegment_084_2362_0034, g32p_row03_traceSegment_084_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2295 67 68, g32p_row03_traceSegment_084_2295_0067, g32p_row03_traceSegment_084_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 2160 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2160 135 135, g32p_row03_traceSegment_084_2160_0135, g32p_row03_traceSegment_084_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2446 8 9, g32p_row03_traceSegment_084_2446_0008, g32p_row03_traceSegment_084_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2430 16 17, g32p_row03_traceSegment_084_2430_0016, g32p_row03_traceSegment_084_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2463 8 9, g32p_row03_traceSegment_084_2463_0008, g32p_row03_traceSegment_084_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2480 8 9, g32p_row03_traceSegment_084_2480_0008, g32p_row03_traceSegment_084_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2463 17 17, g32p_row03_traceSegment_084_2463_0017, g32p_row03_traceSegment_084_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2430 33 34, g32p_row03_traceSegment_084_2430_0033, g32p_row03_traceSegment_084_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2497 8 9, g32p_row03_traceSegment_084_2497_0008, g32p_row03_traceSegment_084_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2514 8 9, g32p_row03_traceSegment_084_2514_0008, g32p_row03_traceSegment_084_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2497 17 17, g32p_row03_traceSegment_084_2497_0017, g32p_row03_traceSegment_084_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2531 8 9, g32p_row03_traceSegment_084_2531_0008, g32p_row03_traceSegment_084_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2548 8 9, g32p_row03_traceSegment_084_2548_0008, g32p_row03_traceSegment_084_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2531 17 17, g32p_row03_traceSegment_084_2531_0017, g32p_row03_traceSegment_084_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2497 34 34, g32p_row03_traceSegment_084_2497_0034, g32p_row03_traceSegment_084_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2430 67 68, g32p_row03_traceSegment_084_2430_0067, g32p_row03_traceSegment_084_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2581 8 9, g32p_row03_traceSegment_084_2581_0008, g32p_row03_traceSegment_084_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2565 16 17, g32p_row03_traceSegment_084_2565_0016, g32p_row03_traceSegment_084_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2598 8 9, g32p_row03_traceSegment_084_2598_0008, g32p_row03_traceSegment_084_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2615 8 9, g32p_row03_traceSegment_084_2615_0008, g32p_row03_traceSegment_084_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2598 17 17, g32p_row03_traceSegment_084_2598_0017, g32p_row03_traceSegment_084_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2565 33 34, g32p_row03_traceSegment_084_2565_0033, g32p_row03_traceSegment_084_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2632 8 9, g32p_row03_traceSegment_084_2632_0008, g32p_row03_traceSegment_084_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2649 8 9, g32p_row03_traceSegment_084_2649_0008, g32p_row03_traceSegment_084_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2632 17 17, g32p_row03_traceSegment_084_2632_0017, g32p_row03_traceSegment_084_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2666 8 9, g32p_row03_traceSegment_084_2666_0008, g32p_row03_traceSegment_084_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2683 8 9, g32p_row03_traceSegment_084_2683_0008, g32p_row03_traceSegment_084_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2666 17 17, g32p_row03_traceSegment_084_2666_0017, g32p_row03_traceSegment_084_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2632 34 34, g32p_row03_traceSegment_084_2632_0034, g32p_row03_traceSegment_084_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2565 67 68, g32p_row03_traceSegment_084_2565_0067, g32p_row03_traceSegment_084_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2430 135 135, g32p_row03_traceSegment_084_2430_0135, g32p_row03_traceSegment_084_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_084 2160 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2160 270 270, g32p_row03_traceSegment_084_2160_0270, g32p_row03_traceSegment_084_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2716 8 9, g32p_row03_traceSegment_084_2716_0008, g32p_row03_traceSegment_084_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2700 16 17, g32p_row03_traceSegment_084_2700_0016, g32p_row03_traceSegment_084_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2733 8 9, g32p_row03_traceSegment_084_2733_0008, g32p_row03_traceSegment_084_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2750 8 9, g32p_row03_traceSegment_084_2750_0008, g32p_row03_traceSegment_084_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2733 17 17, g32p_row03_traceSegment_084_2733_0017, g32p_row03_traceSegment_084_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2700 33 34, g32p_row03_traceSegment_084_2700_0033, g32p_row03_traceSegment_084_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2767 8 9, g32p_row03_traceSegment_084_2767_0008, g32p_row03_traceSegment_084_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2784 8 9, g32p_row03_traceSegment_084_2784_0008, g32p_row03_traceSegment_084_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2767 17 17, g32p_row03_traceSegment_084_2767_0017, g32p_row03_traceSegment_084_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2801 8 9, g32p_row03_traceSegment_084_2801_0008, g32p_row03_traceSegment_084_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2818 8 9, g32p_row03_traceSegment_084_2818_0008, g32p_row03_traceSegment_084_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2801 17 17, g32p_row03_traceSegment_084_2801_0017, g32p_row03_traceSegment_084_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2767 34 34, g32p_row03_traceSegment_084_2767_0034, g32p_row03_traceSegment_084_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2700 67 68, g32p_row03_traceSegment_084_2700_0067, g32p_row03_traceSegment_084_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2851 8 9, g32p_row03_traceSegment_084_2851_0008, g32p_row03_traceSegment_084_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2835 16 17, g32p_row03_traceSegment_084_2835_0016, g32p_row03_traceSegment_084_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2868 8 9, g32p_row03_traceSegment_084_2868_0008, g32p_row03_traceSegment_084_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2885 8 9, g32p_row03_traceSegment_084_2885_0008, g32p_row03_traceSegment_084_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2868 17 17, g32p_row03_traceSegment_084_2868_0017, g32p_row03_traceSegment_084_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2835 33 34, g32p_row03_traceSegment_084_2835_0033, g32p_row03_traceSegment_084_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2902 8 9, g32p_row03_traceSegment_084_2902_0008, g32p_row03_traceSegment_084_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2919 8 9, g32p_row03_traceSegment_084_2919_0008, g32p_row03_traceSegment_084_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2902 17 17, g32p_row03_traceSegment_084_2902_0017, g32p_row03_traceSegment_084_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2936 8 9, g32p_row03_traceSegment_084_2936_0008, g32p_row03_traceSegment_084_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2953 8 9, g32p_row03_traceSegment_084_2953_0008, g32p_row03_traceSegment_084_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2936 17 17, g32p_row03_traceSegment_084_2936_0017, g32p_row03_traceSegment_084_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2902 34 34, g32p_row03_traceSegment_084_2902_0034, g32p_row03_traceSegment_084_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2835 67 68, g32p_row03_traceSegment_084_2835_0067, g32p_row03_traceSegment_084_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2700 135 135, g32p_row03_traceSegment_084_2700_0135, g32p_row03_traceSegment_084_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2986 8 9, g32p_row03_traceSegment_084_2986_0008, g32p_row03_traceSegment_084_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2970 16 17, g32p_row03_traceSegment_084_2970_0016, g32p_row03_traceSegment_084_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3003 8 9, g32p_row03_traceSegment_084_3003_0008, g32p_row03_traceSegment_084_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3020 8 9, g32p_row03_traceSegment_084_3020_0008, g32p_row03_traceSegment_084_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3003 17 17, g32p_row03_traceSegment_084_3003_0017, g32p_row03_traceSegment_084_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2970 33 34, g32p_row03_traceSegment_084_2970_0033, g32p_row03_traceSegment_084_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3037 8 9, g32p_row03_traceSegment_084_3037_0008, g32p_row03_traceSegment_084_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3054 8 9, g32p_row03_traceSegment_084_3054_0008, g32p_row03_traceSegment_084_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3037 17 17, g32p_row03_traceSegment_084_3037_0017, g32p_row03_traceSegment_084_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3071 8 9, g32p_row03_traceSegment_084_3071_0008, g32p_row03_traceSegment_084_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3088 8 9, g32p_row03_traceSegment_084_3088_0008, g32p_row03_traceSegment_084_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3071 17 17, g32p_row03_traceSegment_084_3071_0017, g32p_row03_traceSegment_084_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3037 34 34, g32p_row03_traceSegment_084_3037_0034, g32p_row03_traceSegment_084_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2970 67 68, g32p_row03_traceSegment_084_2970_0067, g32p_row03_traceSegment_084_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3121 8 9, g32p_row03_traceSegment_084_3121_0008, g32p_row03_traceSegment_084_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3105 16 17, g32p_row03_traceSegment_084_3105_0016, g32p_row03_traceSegment_084_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3138 8 9, g32p_row03_traceSegment_084_3138_0008, g32p_row03_traceSegment_084_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3155 8 9, g32p_row03_traceSegment_084_3155_0008, g32p_row03_traceSegment_084_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3138 17 17, g32p_row03_traceSegment_084_3138_0017, g32p_row03_traceSegment_084_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3105 33 34, g32p_row03_traceSegment_084_3105_0033, g32p_row03_traceSegment_084_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3172 8 9, g32p_row03_traceSegment_084_3172_0008, g32p_row03_traceSegment_084_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3189 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3189 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3189 8 9, g32p_row03_traceSegment_084_3189_0008, g32p_row03_traceSegment_084_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3172 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3172 17 17, g32p_row03_traceSegment_084_3172_0017, g32p_row03_traceSegment_084_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3206 8 9, g32p_row03_traceSegment_084_3206_0008, g32p_row03_traceSegment_084_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3223 8 9, g32p_row03_traceSegment_084_3223_0008, g32p_row03_traceSegment_084_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3206 17 17, g32p_row03_traceSegment_084_3206_0017, g32p_row03_traceSegment_084_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 3172 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3172 34 34, g32p_row03_traceSegment_084_3172_0034, g32p_row03_traceSegment_084_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 3105 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3105 67 68, g32p_row03_traceSegment_084_3105_0067, g32p_row03_traceSegment_084_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 2970 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2970 135 135, g32p_row03_traceSegment_084_2970_0135, g32p_row03_traceSegment_084_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_084 2700 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2700 270 270, g32p_row03_traceSegment_084_2700_0270, g32p_row03_traceSegment_084_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_084 2160 1080 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2160 540 540, g32p_row03_traceSegment_084_2160_0540, g32p_row03_traceSegment_084_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3256 8 9, g32p_row03_traceSegment_084_3256_0008, g32p_row03_traceSegment_084_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3240 16 17, g32p_row03_traceSegment_084_3240_0016, g32p_row03_traceSegment_084_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3273 8 9, g32p_row03_traceSegment_084_3273_0008, g32p_row03_traceSegment_084_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3298 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3290 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3290 8 9, g32p_row03_traceSegment_084_3290_0008, g32p_row03_traceSegment_084_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3273 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3273 17 17, g32p_row03_traceSegment_084_3273_0017, g32p_row03_traceSegment_084_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 3240 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3240 33 34, g32p_row03_traceSegment_084_3240_0033, g32p_row03_traceSegment_084_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3307 8 9, g32p_row03_traceSegment_084_3307_0008, g32p_row03_traceSegment_084_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3324 8 9, g32p_row03_traceSegment_084_3324_0008, g32p_row03_traceSegment_084_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3307 17 17, g32p_row03_traceSegment_084_3307_0017, g32p_row03_traceSegment_084_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3341 8 9, g32p_row03_traceSegment_084_3341_0008, g32p_row03_traceSegment_084_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3358 8 9, g32p_row03_traceSegment_084_3358_0008, g32p_row03_traceSegment_084_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3341 17 17, g32p_row03_traceSegment_084_3341_0017, g32p_row03_traceSegment_084_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3307 34 34, g32p_row03_traceSegment_084_3307_0034, g32p_row03_traceSegment_084_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 3240 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3240 67 68, g32p_row03_traceSegment_084_3240_0067, g32p_row03_traceSegment_084_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3399 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3391 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3391 8 9, g32p_row03_traceSegment_084_3391_0008, g32p_row03_traceSegment_084_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 3375 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3375 16 17, g32p_row03_traceSegment_084_3375_0016, g32p_row03_traceSegment_084_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3408 8 9, g32p_row03_traceSegment_084_3408_0008, g32p_row03_traceSegment_084_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3425 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3425 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3425 8 9, g32p_row03_traceSegment_084_3425_0008, g32p_row03_traceSegment_084_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3408 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3408 17 17, g32p_row03_traceSegment_084_3408_0017, g32p_row03_traceSegment_084_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 3375 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3375 33 34, g32p_row03_traceSegment_084_3375_0033, g32p_row03_traceSegment_084_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3442 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3450 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3442 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3442 8 9, g32p_row03_traceSegment_084_3442_0008, g32p_row03_traceSegment_084_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3459 8 9, g32p_row03_traceSegment_084_3459_0008, g32p_row03_traceSegment_084_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3442 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3442 17 17, g32p_row03_traceSegment_084_3442_0017, g32p_row03_traceSegment_084_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3476 8 9, g32p_row03_traceSegment_084_3476_0008, g32p_row03_traceSegment_084_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3501 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3493 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3493 8 9, g32p_row03_traceSegment_084_3493_0008, g32p_row03_traceSegment_084_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3476 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3476 17 17, g32p_row03_traceSegment_084_3476_0017, g32p_row03_traceSegment_084_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 3442 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3442 34 34, g32p_row03_traceSegment_084_3442_0034, g32p_row03_traceSegment_084_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 3375 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3375 67 68, g32p_row03_traceSegment_084_3375_0067, g32p_row03_traceSegment_084_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 3240 270 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3240 135 135, g32p_row03_traceSegment_084_3240_0135, g32p_row03_traceSegment_084_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3526 8 9, g32p_row03_traceSegment_084_3526_0008, g32p_row03_traceSegment_084_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3510 16 17, g32p_row03_traceSegment_084_3510_0016, g32p_row03_traceSegment_084_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3543 8 9, g32p_row03_traceSegment_084_3543_0008, g32p_row03_traceSegment_084_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3568 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3560 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3560 8 9, g32p_row03_traceSegment_084_3560_0008, g32p_row03_traceSegment_084_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3543 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3543 17 17, g32p_row03_traceSegment_084_3543_0017, g32p_row03_traceSegment_084_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 3510 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3510 33 34, g32p_row03_traceSegment_084_3510_0033, g32p_row03_traceSegment_084_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3577 8 9, g32p_row03_traceSegment_084_3577_0008, g32p_row03_traceSegment_084_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3594 8 9, g32p_row03_traceSegment_084_3594_0008, g32p_row03_traceSegment_084_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3577 17 17, g32p_row03_traceSegment_084_3577_0017, g32p_row03_traceSegment_084_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3619 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3611 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3611 8 9, g32p_row03_traceSegment_084_3611_0008, g32p_row03_traceSegment_084_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3628 8 9, g32p_row03_traceSegment_084_3628_0008, g32p_row03_traceSegment_084_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3611 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3611 17 17, g32p_row03_traceSegment_084_3611_0017, g32p_row03_traceSegment_084_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 3577 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3577 34 34, g32p_row03_traceSegment_084_3577_0034, g32p_row03_traceSegment_084_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 3510 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3510 67 68, g32p_row03_traceSegment_084_3510_0067, g32p_row03_traceSegment_084_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 3645 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3661 8 9, g32p_row03_traceSegment_084_3661_0008, g32p_row03_traceSegment_084_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 3645 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3645 16 17, g32p_row03_traceSegment_084_3645_0016, g32p_row03_traceSegment_084_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3678 8 9, g32p_row03_traceSegment_084_3678_0008, g32p_row03_traceSegment_084_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3695 8 9, g32p_row03_traceSegment_084_3695_0008, g32p_row03_traceSegment_084_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3678 17 17, g32p_row03_traceSegment_084_3678_0017, g32p_row03_traceSegment_084_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 3645 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3645 33 34, g32p_row03_traceSegment_084_3645_0033, g32p_row03_traceSegment_084_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3712 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3712 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3712 8 9, g32p_row03_traceSegment_084_3712_0008, g32p_row03_traceSegment_084_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3729 8 9, g32p_row03_traceSegment_084_3729_0008, g32p_row03_traceSegment_084_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3712 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3712 17 17, g32p_row03_traceSegment_084_3712_0017, g32p_row03_traceSegment_084_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3746 8 9, g32p_row03_traceSegment_084_3746_0008, g32p_row03_traceSegment_084_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3763 8 9, g32p_row03_traceSegment_084_3763_0008, g32p_row03_traceSegment_084_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3746 17 17, g32p_row03_traceSegment_084_3746_0017, g32p_row03_traceSegment_084_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 3712 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3712 34 34, g32p_row03_traceSegment_084_3712_0034, g32p_row03_traceSegment_084_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 3645 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3645 67 68, g32p_row03_traceSegment_084_3645_0067, g32p_row03_traceSegment_084_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 3510 270 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3510 135 135, g32p_row03_traceSegment_084_3510_0135, g32p_row03_traceSegment_084_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_084 3240 540 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3240 270 270, g32p_row03_traceSegment_084_3240_0270, g32p_row03_traceSegment_084_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3796 8 9, g32p_row03_traceSegment_084_3796_0008, g32p_row03_traceSegment_084_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3780 16 17, g32p_row03_traceSegment_084_3780_0016, g32p_row03_traceSegment_084_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3813 8 9, g32p_row03_traceSegment_084_3813_0008, g32p_row03_traceSegment_084_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3830 8 9, g32p_row03_traceSegment_084_3830_0008, g32p_row03_traceSegment_084_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3813 17 17, g32p_row03_traceSegment_084_3813_0017, g32p_row03_traceSegment_084_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3780 33 34, g32p_row03_traceSegment_084_3780_0033, g32p_row03_traceSegment_084_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3847 8 9, g32p_row03_traceSegment_084_3847_0008, g32p_row03_traceSegment_084_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3864 8 9, g32p_row03_traceSegment_084_3864_0008, g32p_row03_traceSegment_084_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3847 17 17, g32p_row03_traceSegment_084_3847_0017, g32p_row03_traceSegment_084_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3881 8 9, g32p_row03_traceSegment_084_3881_0008, g32p_row03_traceSegment_084_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3898 8 9, g32p_row03_traceSegment_084_3898_0008, g32p_row03_traceSegment_084_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3881 17 17, g32p_row03_traceSegment_084_3881_0017, g32p_row03_traceSegment_084_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3847 34 34, g32p_row03_traceSegment_084_3847_0034, g32p_row03_traceSegment_084_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3780 67 68, g32p_row03_traceSegment_084_3780_0067, g32p_row03_traceSegment_084_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3931 8 9, g32p_row03_traceSegment_084_3931_0008, g32p_row03_traceSegment_084_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3915 16 17, g32p_row03_traceSegment_084_3915_0016, g32p_row03_traceSegment_084_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3948 8 9, g32p_row03_traceSegment_084_3948_0008, g32p_row03_traceSegment_084_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3965 8 9, g32p_row03_traceSegment_084_3965_0008, g32p_row03_traceSegment_084_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3948 17 17, g32p_row03_traceSegment_084_3948_0017, g32p_row03_traceSegment_084_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3915 33 34, g32p_row03_traceSegment_084_3915_0033, g32p_row03_traceSegment_084_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3982 8 9, g32p_row03_traceSegment_084_3982_0008, g32p_row03_traceSegment_084_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3999 8 9, g32p_row03_traceSegment_084_3999_0008, g32p_row03_traceSegment_084_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3982 17 17, g32p_row03_traceSegment_084_3982_0017, g32p_row03_traceSegment_084_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4016 8 9, g32p_row03_traceSegment_084_4016_0008, g32p_row03_traceSegment_084_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4033 8 9, g32p_row03_traceSegment_084_4033_0008, g32p_row03_traceSegment_084_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4016 17 17, g32p_row03_traceSegment_084_4016_0017, g32p_row03_traceSegment_084_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3982 34 34, g32p_row03_traceSegment_084_3982_0034, g32p_row03_traceSegment_084_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3915 67 68, g32p_row03_traceSegment_084_3915_0067, g32p_row03_traceSegment_084_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3780 135 135, g32p_row03_traceSegment_084_3780_0135, g32p_row03_traceSegment_084_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4066 8 9, g32p_row03_traceSegment_084_4066_0008, g32p_row03_traceSegment_084_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4050 16 17, g32p_row03_traceSegment_084_4050_0016, g32p_row03_traceSegment_084_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4083 8 9, g32p_row03_traceSegment_084_4083_0008, g32p_row03_traceSegment_084_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4100 8 9, g32p_row03_traceSegment_084_4100_0008, g32p_row03_traceSegment_084_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4083 17 17, g32p_row03_traceSegment_084_4083_0017, g32p_row03_traceSegment_084_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4050 33 34, g32p_row03_traceSegment_084_4050_0033, g32p_row03_traceSegment_084_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4117 8 9, g32p_row03_traceSegment_084_4117_0008, g32p_row03_traceSegment_084_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4134 8 9, g32p_row03_traceSegment_084_4134_0008, g32p_row03_traceSegment_084_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4117 17 17, g32p_row03_traceSegment_084_4117_0017, g32p_row03_traceSegment_084_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4151 8 9, g32p_row03_traceSegment_084_4151_0008, g32p_row03_traceSegment_084_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4168 8 9, g32p_row03_traceSegment_084_4168_0008, g32p_row03_traceSegment_084_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4151 17 17, g32p_row03_traceSegment_084_4151_0017, g32p_row03_traceSegment_084_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4117 34 34, g32p_row03_traceSegment_084_4117_0034, g32p_row03_traceSegment_084_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4050 67 68, g32p_row03_traceSegment_084_4050_0067, g32p_row03_traceSegment_084_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_084 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4201 8 9, g32p_row03_traceSegment_084_4201_0008, g32p_row03_traceSegment_084_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_084 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4185 16 17, g32p_row03_traceSegment_084_4185_0016, g32p_row03_traceSegment_084_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4218 8 9, g32p_row03_traceSegment_084_4218_0008, g32p_row03_traceSegment_084_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4243 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4235 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4235 8 9, g32p_row03_traceSegment_084_4235_0008, g32p_row03_traceSegment_084_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 4218 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4218 17 17, g32p_row03_traceSegment_084_4218_0017, g32p_row03_traceSegment_084_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_084 4185 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4185 33 34, g32p_row03_traceSegment_084_4185_0033, g32p_row03_traceSegment_084_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4252 8 9, g32p_row03_traceSegment_084_4252_0008, g32p_row03_traceSegment_084_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4269 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4269 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4269 8 9, g32p_row03_traceSegment_084_4269_0008, g32p_row03_traceSegment_084_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 4252 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4252 17 17, g32p_row03_traceSegment_084_4252_0017, g32p_row03_traceSegment_084_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4286 8 9, g32p_row03_traceSegment_084_4286_0008, g32p_row03_traceSegment_084_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_084 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_084 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_084_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_084 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4303 8 9, g32p_row03_traceSegment_084_4303_0008, g32p_row03_traceSegment_084_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_084 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4286 17 17, g32p_row03_traceSegment_084_4286_0017, g32p_row03_traceSegment_084_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_084 4252 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4252 34 34, g32p_row03_traceSegment_084_4252_0034, g32p_row03_traceSegment_084_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_084 4185 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4185 67 68, g32p_row03_traceSegment_084_4185_0067, g32p_row03_traceSegment_084_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_084_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_084 4050 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 4050 135 135, g32p_row03_traceSegment_084_4050_0135, g32p_row03_traceSegment_084_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_084 3780 540 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3780 270 270, g32p_row03_traceSegment_084_3780_0270, g32p_row03_traceSegment_084_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_084_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_084 3240 1080 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 3240 540 540, g32p_row03_traceSegment_084_3240_0540, g32p_row03_traceSegment_084_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_084_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_084 2160 2160 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 2160 1080 1080, g32p_row03_traceSegment_084_2160_1080, g32p_row03_traceSegment_084_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_084_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_084 0 4320 = [0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_084 0 2160 2160, g32p_row03_traceSegment_084_0000_2160, g32p_row03_traceSegment_084_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 84 = [0, 0, 40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_084_0000_4320

end HodgeLean.Foundations.Program

end
end
