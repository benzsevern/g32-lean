import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0320
import HodgeLean.Foundations.Program.G32PropFourSixPacked0319
import HodgeLean.Foundations.Program.G32PropFourSixPacked0318

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_032 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 32 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_032_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 16 8 9, g32p_row03_traceSegment_032_0016_0008, g32p_row03_traceSegment_032_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 0 16 17, g32p_row03_traceSegment_032_0000_0016, g32p_row03_traceSegment_032_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 33 8 9, g32p_row03_traceSegment_032_0033_0008, g32p_row03_traceSegment_032_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 50 8 9, g32p_row03_traceSegment_032_0050_0008, g32p_row03_traceSegment_032_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 33 17 17, g32p_row03_traceSegment_032_0033_0017, g32p_row03_traceSegment_032_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 0 33 34, g32p_row03_traceSegment_032_0000_0033, g32p_row03_traceSegment_032_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 67 8 9, g32p_row03_traceSegment_032_0067_0008, g32p_row03_traceSegment_032_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 84 8 9, g32p_row03_traceSegment_032_0084_0008, g32p_row03_traceSegment_032_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 67 17 17, g32p_row03_traceSegment_032_0067_0017, g32p_row03_traceSegment_032_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 101 8 9, g32p_row03_traceSegment_032_0101_0008, g32p_row03_traceSegment_032_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 118 8 9, g32p_row03_traceSegment_032_0118_0008, g32p_row03_traceSegment_032_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 101 17 17, g32p_row03_traceSegment_032_0101_0017, g32p_row03_traceSegment_032_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 67 34 34, g32p_row03_traceSegment_032_0067_0034, g32p_row03_traceSegment_032_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 0 67 68, g32p_row03_traceSegment_032_0000_0067, g32p_row03_traceSegment_032_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 151 8 9, g32p_row03_traceSegment_032_0151_0008, g32p_row03_traceSegment_032_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 135 16 17, g32p_row03_traceSegment_032_0135_0016, g32p_row03_traceSegment_032_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 168 8 9, g32p_row03_traceSegment_032_0168_0008, g32p_row03_traceSegment_032_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 185 8 9, g32p_row03_traceSegment_032_0185_0008, g32p_row03_traceSegment_032_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 168 17 17, g32p_row03_traceSegment_032_0168_0017, g32p_row03_traceSegment_032_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 135 33 34, g32p_row03_traceSegment_032_0135_0033, g32p_row03_traceSegment_032_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 202 8 9, g32p_row03_traceSegment_032_0202_0008, g32p_row03_traceSegment_032_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 219 8 9, g32p_row03_traceSegment_032_0219_0008, g32p_row03_traceSegment_032_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 202 17 17, g32p_row03_traceSegment_032_0202_0017, g32p_row03_traceSegment_032_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 236 8 9, g32p_row03_traceSegment_032_0236_0008, g32p_row03_traceSegment_032_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 253 8 9, g32p_row03_traceSegment_032_0253_0008, g32p_row03_traceSegment_032_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 236 17 17, g32p_row03_traceSegment_032_0236_0017, g32p_row03_traceSegment_032_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 202 34 34, g32p_row03_traceSegment_032_0202_0034, g32p_row03_traceSegment_032_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 135 67 68, g32p_row03_traceSegment_032_0135_0067, g32p_row03_traceSegment_032_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 0 135 135, g32p_row03_traceSegment_032_0000_0135, g32p_row03_traceSegment_032_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 286 8 9, g32p_row03_traceSegment_032_0286_0008, g32p_row03_traceSegment_032_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 270 16 17, g32p_row03_traceSegment_032_0270_0016, g32p_row03_traceSegment_032_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 303 8 9, g32p_row03_traceSegment_032_0303_0008, g32p_row03_traceSegment_032_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 320 8 9, g32p_row03_traceSegment_032_0320_0008, g32p_row03_traceSegment_032_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 303 17 17, g32p_row03_traceSegment_032_0303_0017, g32p_row03_traceSegment_032_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 270 33 34, g32p_row03_traceSegment_032_0270_0033, g32p_row03_traceSegment_032_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 337 8 9, g32p_row03_traceSegment_032_0337_0008, g32p_row03_traceSegment_032_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 354 8 9, g32p_row03_traceSegment_032_0354_0008, g32p_row03_traceSegment_032_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 337 17 17, g32p_row03_traceSegment_032_0337_0017, g32p_row03_traceSegment_032_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 371 8 9, g32p_row03_traceSegment_032_0371_0008, g32p_row03_traceSegment_032_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 388 8 9, g32p_row03_traceSegment_032_0388_0008, g32p_row03_traceSegment_032_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 371 17 17, g32p_row03_traceSegment_032_0371_0017, g32p_row03_traceSegment_032_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 337 34 34, g32p_row03_traceSegment_032_0337_0034, g32p_row03_traceSegment_032_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 270 67 68, g32p_row03_traceSegment_032_0270_0067, g32p_row03_traceSegment_032_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 421 8 9, g32p_row03_traceSegment_032_0421_0008, g32p_row03_traceSegment_032_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 405 16 17, g32p_row03_traceSegment_032_0405_0016, g32p_row03_traceSegment_032_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 438 8 9, g32p_row03_traceSegment_032_0438_0008, g32p_row03_traceSegment_032_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 455 8 9, g32p_row03_traceSegment_032_0455_0008, g32p_row03_traceSegment_032_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 438 17 17, g32p_row03_traceSegment_032_0438_0017, g32p_row03_traceSegment_032_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 405 33 34, g32p_row03_traceSegment_032_0405_0033, g32p_row03_traceSegment_032_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 480 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 472 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 472 8 9, g32p_row03_traceSegment_032_0472_0008, g32p_row03_traceSegment_032_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 489 8 9, g32p_row03_traceSegment_032_0489_0008, g32p_row03_traceSegment_032_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 472 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 472 17 17, g32p_row03_traceSegment_032_0472_0017, g32p_row03_traceSegment_032_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 514 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 506 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 506 8 9, g32p_row03_traceSegment_032_0506_0008, g32p_row03_traceSegment_032_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 523 8 9, g32p_row03_traceSegment_032_0523_0008, g32p_row03_traceSegment_032_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 506 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 506 17 17, g32p_row03_traceSegment_032_0506_0017, g32p_row03_traceSegment_032_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 472 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 472 34 34, g32p_row03_traceSegment_032_0472_0034, g32p_row03_traceSegment_032_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 405 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 405 67 68, g32p_row03_traceSegment_032_0405_0067, g32p_row03_traceSegment_032_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 270 270 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 270 135 135, g32p_row03_traceSegment_032_0270_0135, g32p_row03_traceSegment_032_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_032 0 540 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 0 270 270, g32p_row03_traceSegment_032_0000_0270, g32p_row03_traceSegment_032_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 540 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 556 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 556 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 556 8 9, g32p_row03_traceSegment_032_0556_0008, g32p_row03_traceSegment_032_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 540 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 540 16 17, g32p_row03_traceSegment_032_0540_0016, g32p_row03_traceSegment_032_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 573 8 9, g32p_row03_traceSegment_032_0573_0008, g32p_row03_traceSegment_032_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 598 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 590 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 590 8 9, g32p_row03_traceSegment_032_0590_0008, g32p_row03_traceSegment_032_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 573 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 573 17 17, g32p_row03_traceSegment_032_0573_0017, g32p_row03_traceSegment_032_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 540 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 540 33 34, g32p_row03_traceSegment_032_0540_0033, g32p_row03_traceSegment_032_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 615 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 607 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 607 8 9, g32p_row03_traceSegment_032_0607_0008, g32p_row03_traceSegment_032_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 624 8 9, g32p_row03_traceSegment_032_0624_0008, g32p_row03_traceSegment_032_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 607 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 607 17 17, g32p_row03_traceSegment_032_0607_0017, g32p_row03_traceSegment_032_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 641 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 641 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 641 8 9, g32p_row03_traceSegment_032_0641_0008, g32p_row03_traceSegment_032_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 658 8 9, g32p_row03_traceSegment_032_0658_0008, g32p_row03_traceSegment_032_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 641 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 641 17 17, g32p_row03_traceSegment_032_0641_0017, g32p_row03_traceSegment_032_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 607 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 607 34 34, g32p_row03_traceSegment_032_0607_0034, g32p_row03_traceSegment_032_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 540 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 540 67 68, g32p_row03_traceSegment_032_0540_0067, g32p_row03_traceSegment_032_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 675 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 691 8 9, g32p_row03_traceSegment_032_0691_0008, g32p_row03_traceSegment_032_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 675 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 675 16 17, g32p_row03_traceSegment_032_0675_0016, g32p_row03_traceSegment_032_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 708 8 9, g32p_row03_traceSegment_032_0708_0008, g32p_row03_traceSegment_032_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 725 8 9, g32p_row03_traceSegment_032_0725_0008, g32p_row03_traceSegment_032_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 708 17 17, g32p_row03_traceSegment_032_0708_0017, g32p_row03_traceSegment_032_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 675 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 675 33 34, g32p_row03_traceSegment_032_0675_0033, g32p_row03_traceSegment_032_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 742 8 9, g32p_row03_traceSegment_032_0742_0008, g32p_row03_traceSegment_032_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 759 8 9, g32p_row03_traceSegment_032_0759_0008, g32p_row03_traceSegment_032_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 742 17 17, g32p_row03_traceSegment_032_0742_0017, g32p_row03_traceSegment_032_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 776 8 9, g32p_row03_traceSegment_032_0776_0008, g32p_row03_traceSegment_032_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 793 8 9, g32p_row03_traceSegment_032_0793_0008, g32p_row03_traceSegment_032_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 776 17 17, g32p_row03_traceSegment_032_0776_0017, g32p_row03_traceSegment_032_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 742 34 34, g32p_row03_traceSegment_032_0742_0034, g32p_row03_traceSegment_032_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 675 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 675 67 68, g32p_row03_traceSegment_032_0675_0067, g32p_row03_traceSegment_032_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 540 270 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 540 135 135, g32p_row03_traceSegment_032_0540_0135, g32p_row03_traceSegment_032_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 826 8 9, g32p_row03_traceSegment_032_0826_0008, g32p_row03_traceSegment_032_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 810 16 17, g32p_row03_traceSegment_032_0810_0016, g32p_row03_traceSegment_032_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 843 8 9, g32p_row03_traceSegment_032_0843_0008, g32p_row03_traceSegment_032_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 860 8 9, g32p_row03_traceSegment_032_0860_0008, g32p_row03_traceSegment_032_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 843 17 17, g32p_row03_traceSegment_032_0843_0017, g32p_row03_traceSegment_032_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 810 33 34, g32p_row03_traceSegment_032_0810_0033, g32p_row03_traceSegment_032_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 877 8 9, g32p_row03_traceSegment_032_0877_0008, g32p_row03_traceSegment_032_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 894 8 9, g32p_row03_traceSegment_032_0894_0008, g32p_row03_traceSegment_032_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 877 17 17, g32p_row03_traceSegment_032_0877_0017, g32p_row03_traceSegment_032_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 911 8 9, g32p_row03_traceSegment_032_0911_0008, g32p_row03_traceSegment_032_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 928 8 9, g32p_row03_traceSegment_032_0928_0008, g32p_row03_traceSegment_032_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 911 17 17, g32p_row03_traceSegment_032_0911_0017, g32p_row03_traceSegment_032_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 877 34 34, g32p_row03_traceSegment_032_0877_0034, g32p_row03_traceSegment_032_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 810 67 68, g32p_row03_traceSegment_032_0810_0067, g32p_row03_traceSegment_032_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 961 8 9, g32p_row03_traceSegment_032_0961_0008, g32p_row03_traceSegment_032_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 945 16 17, g32p_row03_traceSegment_032_0945_0016, g32p_row03_traceSegment_032_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 978 8 9, g32p_row03_traceSegment_032_0978_0008, g32p_row03_traceSegment_032_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 995 8 9, g32p_row03_traceSegment_032_0995_0008, g32p_row03_traceSegment_032_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 978 17 17, g32p_row03_traceSegment_032_0978_0017, g32p_row03_traceSegment_032_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 945 33 34, g32p_row03_traceSegment_032_0945_0033, g32p_row03_traceSegment_032_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1012 8 9, g32p_row03_traceSegment_032_1012_0008, g32p_row03_traceSegment_032_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1029 8 9, g32p_row03_traceSegment_032_1029_0008, g32p_row03_traceSegment_032_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1012 17 17, g32p_row03_traceSegment_032_1012_0017, g32p_row03_traceSegment_032_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1046 8 9, g32p_row03_traceSegment_032_1046_0008, g32p_row03_traceSegment_032_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1063 8 9, g32p_row03_traceSegment_032_1063_0008, g32p_row03_traceSegment_032_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1046 17 17, g32p_row03_traceSegment_032_1046_0017, g32p_row03_traceSegment_032_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1012 34 34, g32p_row03_traceSegment_032_1012_0034, g32p_row03_traceSegment_032_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 945 67 68, g32p_row03_traceSegment_032_0945_0067, g32p_row03_traceSegment_032_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 810 135 135, g32p_row03_traceSegment_032_0810_0135, g32p_row03_traceSegment_032_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_032 540 540 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 540 270 270, g32p_row03_traceSegment_032_0540_0270, g32p_row03_traceSegment_032_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_032 0 1080 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 0 540 540, g32p_row03_traceSegment_032_0000_0540, g32p_row03_traceSegment_032_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1096 8 9, g32p_row03_traceSegment_032_1096_0008, g32p_row03_traceSegment_032_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1080 16 17, g32p_row03_traceSegment_032_1080_0016, g32p_row03_traceSegment_032_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1113 8 9, g32p_row03_traceSegment_032_1113_0008, g32p_row03_traceSegment_032_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1130 8 9, g32p_row03_traceSegment_032_1130_0008, g32p_row03_traceSegment_032_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1113 17 17, g32p_row03_traceSegment_032_1113_0017, g32p_row03_traceSegment_032_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1080 33 34, g32p_row03_traceSegment_032_1080_0033, g32p_row03_traceSegment_032_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1147 8 9, g32p_row03_traceSegment_032_1147_0008, g32p_row03_traceSegment_032_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1164 8 9, g32p_row03_traceSegment_032_1164_0008, g32p_row03_traceSegment_032_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1147 17 17, g32p_row03_traceSegment_032_1147_0017, g32p_row03_traceSegment_032_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1181 8 9, g32p_row03_traceSegment_032_1181_0008, g32p_row03_traceSegment_032_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1198 8 9, g32p_row03_traceSegment_032_1198_0008, g32p_row03_traceSegment_032_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1181 17 17, g32p_row03_traceSegment_032_1181_0017, g32p_row03_traceSegment_032_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1147 34 34, g32p_row03_traceSegment_032_1147_0034, g32p_row03_traceSegment_032_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1080 67 68, g32p_row03_traceSegment_032_1080_0067, g32p_row03_traceSegment_032_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1231 8 9, g32p_row03_traceSegment_032_1231_0008, g32p_row03_traceSegment_032_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1215 16 17, g32p_row03_traceSegment_032_1215_0016, g32p_row03_traceSegment_032_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1248 8 9, g32p_row03_traceSegment_032_1248_0008, g32p_row03_traceSegment_032_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1265 8 9, g32p_row03_traceSegment_032_1265_0008, g32p_row03_traceSegment_032_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1248 17 17, g32p_row03_traceSegment_032_1248_0017, g32p_row03_traceSegment_032_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1215 33 34, g32p_row03_traceSegment_032_1215_0033, g32p_row03_traceSegment_032_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1282 8 9, g32p_row03_traceSegment_032_1282_0008, g32p_row03_traceSegment_032_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1299 8 9, g32p_row03_traceSegment_032_1299_0008, g32p_row03_traceSegment_032_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1282 17 17, g32p_row03_traceSegment_032_1282_0017, g32p_row03_traceSegment_032_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1316 8 9, g32p_row03_traceSegment_032_1316_0008, g32p_row03_traceSegment_032_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1333 8 9, g32p_row03_traceSegment_032_1333_0008, g32p_row03_traceSegment_032_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1316 17 17, g32p_row03_traceSegment_032_1316_0017, g32p_row03_traceSegment_032_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1282 34 34, g32p_row03_traceSegment_032_1282_0034, g32p_row03_traceSegment_032_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1215 67 68, g32p_row03_traceSegment_032_1215_0067, g32p_row03_traceSegment_032_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1080 135 135, g32p_row03_traceSegment_032_1080_0135, g32p_row03_traceSegment_032_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1366 8 9, g32p_row03_traceSegment_032_1366_0008, g32p_row03_traceSegment_032_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1350 16 17, g32p_row03_traceSegment_032_1350_0016, g32p_row03_traceSegment_032_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1391 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1383 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1383 8 9, g32p_row03_traceSegment_032_1383_0008, g32p_row03_traceSegment_032_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1400 8 9, g32p_row03_traceSegment_032_1400_0008, g32p_row03_traceSegment_032_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1383 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1383 17 17, g32p_row03_traceSegment_032_1383_0017, g32p_row03_traceSegment_032_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 1350 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1350 33 34, g32p_row03_traceSegment_032_1350_0033, g32p_row03_traceSegment_032_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1417 8 9, g32p_row03_traceSegment_032_1417_0008, g32p_row03_traceSegment_032_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1434 8 9, g32p_row03_traceSegment_032_1434_0008, g32p_row03_traceSegment_032_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1417 17 17, g32p_row03_traceSegment_032_1417_0017, g32p_row03_traceSegment_032_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1459 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1451 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1451 8 9, g32p_row03_traceSegment_032_1451_0008, g32p_row03_traceSegment_032_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1468 8 9, g32p_row03_traceSegment_032_1468_0008, g32p_row03_traceSegment_032_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1451 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1451 17 17, g32p_row03_traceSegment_032_1451_0017, g32p_row03_traceSegment_032_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 1417 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1417 34 34, g32p_row03_traceSegment_032_1417_0034, g32p_row03_traceSegment_032_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 1350 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1350 67 68, g32p_row03_traceSegment_032_1350_0067, g32p_row03_traceSegment_032_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1501 8 9, g32p_row03_traceSegment_032_1501_0008, g32p_row03_traceSegment_032_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1485 16 17, g32p_row03_traceSegment_032_1485_0016, g32p_row03_traceSegment_032_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1518 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1526 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1518 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1518 8 9, g32p_row03_traceSegment_032_1518_0008, g32p_row03_traceSegment_032_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1535 8 9, g32p_row03_traceSegment_032_1535_0008, g32p_row03_traceSegment_032_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1518 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1518 17 17, g32p_row03_traceSegment_032_1518_0017, g32p_row03_traceSegment_032_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 1485 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1485 33 34, g32p_row03_traceSegment_032_1485_0033, g32p_row03_traceSegment_032_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1552 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1552 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1552 8 9, g32p_row03_traceSegment_032_1552_0008, g32p_row03_traceSegment_032_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1569 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1569 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1569 8 9, g32p_row03_traceSegment_032_1569_0008, g32p_row03_traceSegment_032_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1552 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1552 17 17, g32p_row03_traceSegment_032_1552_0017, g32p_row03_traceSegment_032_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1594 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1586 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1586 8 9, g32p_row03_traceSegment_032_1586_0008, g32p_row03_traceSegment_032_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1603 8 9, g32p_row03_traceSegment_032_1603_0008, g32p_row03_traceSegment_032_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1586 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1586 17 17, g32p_row03_traceSegment_032_1586_0017, g32p_row03_traceSegment_032_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 1552 68 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1552 34 34, g32p_row03_traceSegment_032_1552_0034, g32p_row03_traceSegment_032_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 1485 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1485 67 68, g32p_row03_traceSegment_032_1485_0067, g32p_row03_traceSegment_032_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 1350 270 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1350 135 135, g32p_row03_traceSegment_032_1350_0135, g32p_row03_traceSegment_032_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_032 1080 540 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1080 270 270, g32p_row03_traceSegment_032_1080_0270, g32p_row03_traceSegment_032_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1636 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1636 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1636 8 9, g32p_row03_traceSegment_032_1636_0008, g32p_row03_traceSegment_032_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 1620 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1620 16 17, g32p_row03_traceSegment_032_1620_0016, g32p_row03_traceSegment_032_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1653 8 9, g32p_row03_traceSegment_032_1653_0008, g32p_row03_traceSegment_032_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1670 8 9, g32p_row03_traceSegment_032_1670_0008, g32p_row03_traceSegment_032_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1653 17 17, g32p_row03_traceSegment_032_1653_0017, g32p_row03_traceSegment_032_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 1620 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1620 33 34, g32p_row03_traceSegment_032_1620_0033, g32p_row03_traceSegment_032_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1687 8 9, g32p_row03_traceSegment_032_1687_0008, g32p_row03_traceSegment_032_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1704 8 9, g32p_row03_traceSegment_032_1704_0008, g32p_row03_traceSegment_032_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1687 17 17, g32p_row03_traceSegment_032_1687_0017, g32p_row03_traceSegment_032_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1721 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1721 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1721 8 9, g32p_row03_traceSegment_032_1721_0008, g32p_row03_traceSegment_032_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1746 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1738 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1738 8 9, g32p_row03_traceSegment_032_1738_0008, g32p_row03_traceSegment_032_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1721 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1721 17 17, g32p_row03_traceSegment_032_1721_0017, g32p_row03_traceSegment_032_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 1687 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1687 34 34, g32p_row03_traceSegment_032_1687_0034, g32p_row03_traceSegment_032_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 1620 135 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1620 67 68, g32p_row03_traceSegment_032_1620_0067, g32p_row03_traceSegment_032_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1779 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1771 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1771 8 9, g32p_row03_traceSegment_032_1771_0008, g32p_row03_traceSegment_032_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 1755 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1755 16 17, g32p_row03_traceSegment_032_1755_0016, g32p_row03_traceSegment_032_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1788 8 9, g32p_row03_traceSegment_032_1788_0008, g32p_row03_traceSegment_032_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1813 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1805 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1805 8 9, g32p_row03_traceSegment_032_1805_0008, g32p_row03_traceSegment_032_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1788 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1788 17 17, g32p_row03_traceSegment_032_1788_0017, g32p_row03_traceSegment_032_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 1755 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1755 33 34, g32p_row03_traceSegment_032_1755_0033, g32p_row03_traceSegment_032_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1822 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1822 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1822 8 9, g32p_row03_traceSegment_032_1822_0008, g32p_row03_traceSegment_032_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1839 8 9, g32p_row03_traceSegment_032_1839_0008, g32p_row03_traceSegment_032_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1822 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1822 17 17, g32p_row03_traceSegment_032_1822_0017, g32p_row03_traceSegment_032_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1864 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1856 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1856 8 9, g32p_row03_traceSegment_032_1856_0008, g32p_row03_traceSegment_032_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1873 8 9, g32p_row03_traceSegment_032_1873_0008, g32p_row03_traceSegment_032_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1856 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1856 17 17, g32p_row03_traceSegment_032_1856_0017, g32p_row03_traceSegment_032_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 1822 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1822 34 34, g32p_row03_traceSegment_032_1822_0034, g32p_row03_traceSegment_032_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 1755 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1755 67 68, g32p_row03_traceSegment_032_1755_0067, g32p_row03_traceSegment_032_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 1620 270 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1620 135 135, g32p_row03_traceSegment_032_1620_0135, g32p_row03_traceSegment_032_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1906 8 9, g32p_row03_traceSegment_032_1906_0008, g32p_row03_traceSegment_032_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1890 16 17, g32p_row03_traceSegment_032_1890_0016, g32p_row03_traceSegment_032_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1931 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1923 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1923 8 9, g32p_row03_traceSegment_032_1923_0008, g32p_row03_traceSegment_032_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1940 8 9, g32p_row03_traceSegment_032_1940_0008, g32p_row03_traceSegment_032_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1923 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1923 17 17, g32p_row03_traceSegment_032_1923_0017, g32p_row03_traceSegment_032_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 1890 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1890 33 34, g32p_row03_traceSegment_032_1890_0033, g32p_row03_traceSegment_032_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1957 8 9, g32p_row03_traceSegment_032_1957_0008, g32p_row03_traceSegment_032_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1974 8 9, g32p_row03_traceSegment_032_1974_0008, g32p_row03_traceSegment_032_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1957 17 17, g32p_row03_traceSegment_032_1957_0017, g32p_row03_traceSegment_032_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1991 8 9, g32p_row03_traceSegment_032_1991_0008, g32p_row03_traceSegment_032_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2008 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2008 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2008 8 9, g32p_row03_traceSegment_032_2008_0008, g32p_row03_traceSegment_032_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 1991 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1991 17 17, g32p_row03_traceSegment_032_1991_0017, g32p_row03_traceSegment_032_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 1957 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1957 34 34, g32p_row03_traceSegment_032_1957_0034, g32p_row03_traceSegment_032_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 1890 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1890 67 68, g32p_row03_traceSegment_032_1890_0067, g32p_row03_traceSegment_032_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2041 8 9, g32p_row03_traceSegment_032_2041_0008, g32p_row03_traceSegment_032_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2025 16 17, g32p_row03_traceSegment_032_2025_0016, g32p_row03_traceSegment_032_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2058 8 9, g32p_row03_traceSegment_032_2058_0008, g32p_row03_traceSegment_032_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2075 8 9, g32p_row03_traceSegment_032_2075_0008, g32p_row03_traceSegment_032_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2058 17 17, g32p_row03_traceSegment_032_2058_0017, g32p_row03_traceSegment_032_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2025 33 34, g32p_row03_traceSegment_032_2025_0033, g32p_row03_traceSegment_032_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2092 8 9, g32p_row03_traceSegment_032_2092_0008, g32p_row03_traceSegment_032_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2109 8 9, g32p_row03_traceSegment_032_2109_0008, g32p_row03_traceSegment_032_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2092 17 17, g32p_row03_traceSegment_032_2092_0017, g32p_row03_traceSegment_032_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2126 8 9, g32p_row03_traceSegment_032_2126_0008, g32p_row03_traceSegment_032_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2143 8 9, g32p_row03_traceSegment_032_2143_0008, g32p_row03_traceSegment_032_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2126 17 17, g32p_row03_traceSegment_032_2126_0017, g32p_row03_traceSegment_032_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2092 34 34, g32p_row03_traceSegment_032_2092_0034, g32p_row03_traceSegment_032_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2025 67 68, g32p_row03_traceSegment_032_2025_0067, g32p_row03_traceSegment_032_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 1890 270 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1890 135 135, g32p_row03_traceSegment_032_1890_0135, g32p_row03_traceSegment_032_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_032 1620 540 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1620 270 270, g32p_row03_traceSegment_032_1620_0270, g32p_row03_traceSegment_032_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_032_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_032 1080 1080 = [0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 1080 540 540, g32p_row03_traceSegment_032_1080_0540, g32p_row03_traceSegment_032_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_032 0 2160 = [0, 0, 0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 0 1080 1080, g32p_row03_traceSegment_032_0000_1080, g32p_row03_traceSegment_032_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2176 8 9, g32p_row03_traceSegment_032_2176_0008, g32p_row03_traceSegment_032_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2160 16 17, g32p_row03_traceSegment_032_2160_0016, g32p_row03_traceSegment_032_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2193 8 9, g32p_row03_traceSegment_032_2193_0008, g32p_row03_traceSegment_032_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2218 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2210 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2210 8 9, g32p_row03_traceSegment_032_2210_0008, g32p_row03_traceSegment_032_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2193 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2193 17 17, g32p_row03_traceSegment_032_2193_0017, g32p_row03_traceSegment_032_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 2160 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2160 33 34, g32p_row03_traceSegment_032_2160_0033, g32p_row03_traceSegment_032_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2227 8 9, g32p_row03_traceSegment_032_2227_0008, g32p_row03_traceSegment_032_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2244 8 9, g32p_row03_traceSegment_032_2244_0008, g32p_row03_traceSegment_032_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2227 17 17, g32p_row03_traceSegment_032_2227_0017, g32p_row03_traceSegment_032_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2261 8 9, g32p_row03_traceSegment_032_2261_0008, g32p_row03_traceSegment_032_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2278 8 9, g32p_row03_traceSegment_032_2278_0008, g32p_row03_traceSegment_032_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2261 17 17, g32p_row03_traceSegment_032_2261_0017, g32p_row03_traceSegment_032_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2227 34 34, g32p_row03_traceSegment_032_2227_0034, g32p_row03_traceSegment_032_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 2160 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2160 67 68, g32p_row03_traceSegment_032_2160_0067, g32p_row03_traceSegment_032_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2311 8 9, g32p_row03_traceSegment_032_2311_0008, g32p_row03_traceSegment_032_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2295 16 17, g32p_row03_traceSegment_032_2295_0016, g32p_row03_traceSegment_032_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2328 8 9, g32p_row03_traceSegment_032_2328_0008, g32p_row03_traceSegment_032_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2345 8 9, g32p_row03_traceSegment_032_2345_0008, g32p_row03_traceSegment_032_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2328 17 17, g32p_row03_traceSegment_032_2328_0017, g32p_row03_traceSegment_032_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2295 33 34, g32p_row03_traceSegment_032_2295_0033, g32p_row03_traceSegment_032_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2362 8 9, g32p_row03_traceSegment_032_2362_0008, g32p_row03_traceSegment_032_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2379 8 9, g32p_row03_traceSegment_032_2379_0008, g32p_row03_traceSegment_032_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2362 17 17, g32p_row03_traceSegment_032_2362_0017, g32p_row03_traceSegment_032_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2396 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2396 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2396 8 9, g32p_row03_traceSegment_032_2396_0008, g32p_row03_traceSegment_032_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2413 8 9, g32p_row03_traceSegment_032_2413_0008, g32p_row03_traceSegment_032_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2396 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2396 17 17, g32p_row03_traceSegment_032_2396_0017, g32p_row03_traceSegment_032_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 2362 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2362 34 34, g32p_row03_traceSegment_032_2362_0034, g32p_row03_traceSegment_032_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 2295 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2295 67 68, g32p_row03_traceSegment_032_2295_0067, g32p_row03_traceSegment_032_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 2160 270 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2160 135 135, g32p_row03_traceSegment_032_2160_0135, g32p_row03_traceSegment_032_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2446 8 9, g32p_row03_traceSegment_032_2446_0008, g32p_row03_traceSegment_032_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2430 16 17, g32p_row03_traceSegment_032_2430_0016, g32p_row03_traceSegment_032_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2463 8 9, g32p_row03_traceSegment_032_2463_0008, g32p_row03_traceSegment_032_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2480 8 9, g32p_row03_traceSegment_032_2480_0008, g32p_row03_traceSegment_032_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2463 17 17, g32p_row03_traceSegment_032_2463_0017, g32p_row03_traceSegment_032_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2430 33 34, g32p_row03_traceSegment_032_2430_0033, g32p_row03_traceSegment_032_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2497 8 9, g32p_row03_traceSegment_032_2497_0008, g32p_row03_traceSegment_032_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2514 8 9, g32p_row03_traceSegment_032_2514_0008, g32p_row03_traceSegment_032_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2497 17 17, g32p_row03_traceSegment_032_2497_0017, g32p_row03_traceSegment_032_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2531 8 9, g32p_row03_traceSegment_032_2531_0008, g32p_row03_traceSegment_032_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2548 8 9, g32p_row03_traceSegment_032_2548_0008, g32p_row03_traceSegment_032_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2531 17 17, g32p_row03_traceSegment_032_2531_0017, g32p_row03_traceSegment_032_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2497 34 34, g32p_row03_traceSegment_032_2497_0034, g32p_row03_traceSegment_032_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2430 67 68, g32p_row03_traceSegment_032_2430_0067, g32p_row03_traceSegment_032_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2581 8 9, g32p_row03_traceSegment_032_2581_0008, g32p_row03_traceSegment_032_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2565 16 17, g32p_row03_traceSegment_032_2565_0016, g32p_row03_traceSegment_032_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2598 8 9, g32p_row03_traceSegment_032_2598_0008, g32p_row03_traceSegment_032_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2615 8 9, g32p_row03_traceSegment_032_2615_0008, g32p_row03_traceSegment_032_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2598 17 17, g32p_row03_traceSegment_032_2598_0017, g32p_row03_traceSegment_032_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2565 33 34, g32p_row03_traceSegment_032_2565_0033, g32p_row03_traceSegment_032_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2632 8 9, g32p_row03_traceSegment_032_2632_0008, g32p_row03_traceSegment_032_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2657 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2649 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2649 8 9, g32p_row03_traceSegment_032_2649_0008, g32p_row03_traceSegment_032_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2632 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2632 17 17, g32p_row03_traceSegment_032_2632_0017, g32p_row03_traceSegment_032_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2666 8 9, g32p_row03_traceSegment_032_2666_0008, g32p_row03_traceSegment_032_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2683 8 9, g32p_row03_traceSegment_032_2683_0008, g32p_row03_traceSegment_032_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2666 17 17, g32p_row03_traceSegment_032_2666_0017, g32p_row03_traceSegment_032_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 2632 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2632 34 34, g32p_row03_traceSegment_032_2632_0034, g32p_row03_traceSegment_032_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 2565 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2565 67 68, g32p_row03_traceSegment_032_2565_0067, g32p_row03_traceSegment_032_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 2430 270 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2430 135 135, g32p_row03_traceSegment_032_2430_0135, g32p_row03_traceSegment_032_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_032 2160 540 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2160 270 270, g32p_row03_traceSegment_032_2160_0270, g32p_row03_traceSegment_032_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2716 8 9, g32p_row03_traceSegment_032_2716_0008, g32p_row03_traceSegment_032_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2700 16 17, g32p_row03_traceSegment_032_2700_0016, g32p_row03_traceSegment_032_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2733 8 9, g32p_row03_traceSegment_032_2733_0008, g32p_row03_traceSegment_032_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2750 8 9, g32p_row03_traceSegment_032_2750_0008, g32p_row03_traceSegment_032_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2733 17 17, g32p_row03_traceSegment_032_2733_0017, g32p_row03_traceSegment_032_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2700 33 34, g32p_row03_traceSegment_032_2700_0033, g32p_row03_traceSegment_032_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2767 8 9, g32p_row03_traceSegment_032_2767_0008, g32p_row03_traceSegment_032_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2784 8 9, g32p_row03_traceSegment_032_2784_0008, g32p_row03_traceSegment_032_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2767 17 17, g32p_row03_traceSegment_032_2767_0017, g32p_row03_traceSegment_032_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2801 8 9, g32p_row03_traceSegment_032_2801_0008, g32p_row03_traceSegment_032_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2818 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2818 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2818 8 9, g32p_row03_traceSegment_032_2818_0008, g32p_row03_traceSegment_032_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2801 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2801 17 17, g32p_row03_traceSegment_032_2801_0017, g32p_row03_traceSegment_032_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 2767 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2767 34 34, g32p_row03_traceSegment_032_2767_0034, g32p_row03_traceSegment_032_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 2700 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2700 67 68, g32p_row03_traceSegment_032_2700_0067, g32p_row03_traceSegment_032_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2851 8 9, g32p_row03_traceSegment_032_2851_0008, g32p_row03_traceSegment_032_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2835 16 17, g32p_row03_traceSegment_032_2835_0016, g32p_row03_traceSegment_032_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2868 8 9, g32p_row03_traceSegment_032_2868_0008, g32p_row03_traceSegment_032_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2885 8 9, g32p_row03_traceSegment_032_2885_0008, g32p_row03_traceSegment_032_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2868 17 17, g32p_row03_traceSegment_032_2868_0017, g32p_row03_traceSegment_032_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2835 33 34, g32p_row03_traceSegment_032_2835_0033, g32p_row03_traceSegment_032_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2902 8 9, g32p_row03_traceSegment_032_2902_0008, g32p_row03_traceSegment_032_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2919 8 9, g32p_row03_traceSegment_032_2919_0008, g32p_row03_traceSegment_032_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2902 17 17, g32p_row03_traceSegment_032_2902_0017, g32p_row03_traceSegment_032_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2936 8 9, g32p_row03_traceSegment_032_2936_0008, g32p_row03_traceSegment_032_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2953 8 9, g32p_row03_traceSegment_032_2953_0008, g32p_row03_traceSegment_032_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2936 17 17, g32p_row03_traceSegment_032_2936_0017, g32p_row03_traceSegment_032_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2902 34 34, g32p_row03_traceSegment_032_2902_0034, g32p_row03_traceSegment_032_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2835 67 68, g32p_row03_traceSegment_032_2835_0067, g32p_row03_traceSegment_032_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 2700 270 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2700 135 135, g32p_row03_traceSegment_032_2700_0135, g32p_row03_traceSegment_032_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 2970 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 2994 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 2986 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2986 8 9, g32p_row03_traceSegment_032_2986_0008, g32p_row03_traceSegment_032_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 2970 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2970 16 17, g32p_row03_traceSegment_032_2970_0016, g32p_row03_traceSegment_032_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3003 8 9, g32p_row03_traceSegment_032_3003_0008, g32p_row03_traceSegment_032_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3020 8 9, g32p_row03_traceSegment_032_3020_0008, g32p_row03_traceSegment_032_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3003 17 17, g32p_row03_traceSegment_032_3003_0017, g32p_row03_traceSegment_032_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 2970 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2970 33 34, g32p_row03_traceSegment_032_2970_0033, g32p_row03_traceSegment_032_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3037 8 9, g32p_row03_traceSegment_032_3037_0008, g32p_row03_traceSegment_032_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3054 8 9, g32p_row03_traceSegment_032_3054_0008, g32p_row03_traceSegment_032_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3037 17 17, g32p_row03_traceSegment_032_3037_0017, g32p_row03_traceSegment_032_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3071 8 9, g32p_row03_traceSegment_032_3071_0008, g32p_row03_traceSegment_032_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3088 8 9, g32p_row03_traceSegment_032_3088_0008, g32p_row03_traceSegment_032_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3071 17 17, g32p_row03_traceSegment_032_3071_0017, g32p_row03_traceSegment_032_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3037 34 34, g32p_row03_traceSegment_032_3037_0034, g32p_row03_traceSegment_032_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 2970 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2970 67 68, g32p_row03_traceSegment_032_2970_0067, g32p_row03_traceSegment_032_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3121 8 9, g32p_row03_traceSegment_032_3121_0008, g32p_row03_traceSegment_032_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3105 16 17, g32p_row03_traceSegment_032_3105_0016, g32p_row03_traceSegment_032_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3138 8 9, g32p_row03_traceSegment_032_3138_0008, g32p_row03_traceSegment_032_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3155 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3155 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3155 8 9, g32p_row03_traceSegment_032_3155_0008, g32p_row03_traceSegment_032_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3138 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3138 17 17, g32p_row03_traceSegment_032_3138_0017, g32p_row03_traceSegment_032_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 3105 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3105 33 34, g32p_row03_traceSegment_032_3105_0033, g32p_row03_traceSegment_032_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3172 8 9, g32p_row03_traceSegment_032_3172_0008, g32p_row03_traceSegment_032_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3189 8 9, g32p_row03_traceSegment_032_3189_0008, g32p_row03_traceSegment_032_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3172 17 17, g32p_row03_traceSegment_032_3172_0017, g32p_row03_traceSegment_032_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3206 8 9, g32p_row03_traceSegment_032_3206_0008, g32p_row03_traceSegment_032_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3223 8 9, g32p_row03_traceSegment_032_3223_0008, g32p_row03_traceSegment_032_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3206 17 17, g32p_row03_traceSegment_032_3206_0017, g32p_row03_traceSegment_032_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3172 34 34, g32p_row03_traceSegment_032_3172_0034, g32p_row03_traceSegment_032_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 3105 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3105 67 68, g32p_row03_traceSegment_032_3105_0067, g32p_row03_traceSegment_032_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 2970 270 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2970 135 135, g32p_row03_traceSegment_032_2970_0135, g32p_row03_traceSegment_032_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_032 2700 540 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2700 270 270, g32p_row03_traceSegment_032_2700_0270, g32p_row03_traceSegment_032_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_032 2160 1080 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2160 540 540, g32p_row03_traceSegment_032_2160_0540, g32p_row03_traceSegment_032_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3256 8 9, g32p_row03_traceSegment_032_3256_0008, g32p_row03_traceSegment_032_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3240 16 17, g32p_row03_traceSegment_032_3240_0016, g32p_row03_traceSegment_032_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3273 8 9, g32p_row03_traceSegment_032_3273_0008, g32p_row03_traceSegment_032_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3290 8 9, g32p_row03_traceSegment_032_3290_0008, g32p_row03_traceSegment_032_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3273 17 17, g32p_row03_traceSegment_032_3273_0017, g32p_row03_traceSegment_032_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3240 33 34, g32p_row03_traceSegment_032_3240_0033, g32p_row03_traceSegment_032_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3307 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3307 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3307 8 9, g32p_row03_traceSegment_032_3307_0008, g32p_row03_traceSegment_032_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3324 8 9, g32p_row03_traceSegment_032_3324_0008, g32p_row03_traceSegment_032_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3307 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3307 17 17, g32p_row03_traceSegment_032_3307_0017, g32p_row03_traceSegment_032_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3349 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3341 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3341 8 9, g32p_row03_traceSegment_032_3341_0008, g32p_row03_traceSegment_032_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3358 8 9, g32p_row03_traceSegment_032_3358_0008, g32p_row03_traceSegment_032_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3341 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3341 17 17, g32p_row03_traceSegment_032_3341_0017, g32p_row03_traceSegment_032_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 3307 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3307 34 34, g32p_row03_traceSegment_032_3307_0034, g32p_row03_traceSegment_032_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 3240 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3240 67 68, g32p_row03_traceSegment_032_3240_0067, g32p_row03_traceSegment_032_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3391 8 9, g32p_row03_traceSegment_032_3391_0008, g32p_row03_traceSegment_032_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3375 16 17, g32p_row03_traceSegment_032_3375_0016, g32p_row03_traceSegment_032_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3408 8 9, g32p_row03_traceSegment_032_3408_0008, g32p_row03_traceSegment_032_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3425 8 9, g32p_row03_traceSegment_032_3425_0008, g32p_row03_traceSegment_032_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3408 17 17, g32p_row03_traceSegment_032_3408_0017, g32p_row03_traceSegment_032_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3375 33 34, g32p_row03_traceSegment_032_3375_0033, g32p_row03_traceSegment_032_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3442 8 9, g32p_row03_traceSegment_032_3442_0008, g32p_row03_traceSegment_032_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3459 8 9, g32p_row03_traceSegment_032_3459_0008, g32p_row03_traceSegment_032_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3442 17 17, g32p_row03_traceSegment_032_3442_0017, g32p_row03_traceSegment_032_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3476 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3476 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3476 8 9, g32p_row03_traceSegment_032_3476_0008, g32p_row03_traceSegment_032_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3493 8 9, g32p_row03_traceSegment_032_3493_0008, g32p_row03_traceSegment_032_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3476 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3476 17 17, g32p_row03_traceSegment_032_3476_0017, g32p_row03_traceSegment_032_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 3442 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3442 34 34, g32p_row03_traceSegment_032_3442_0034, g32p_row03_traceSegment_032_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 3375 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3375 67 68, g32p_row03_traceSegment_032_3375_0067, g32p_row03_traceSegment_032_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 3240 270 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3240 135 135, g32p_row03_traceSegment_032_3240_0135, g32p_row03_traceSegment_032_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3526 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3526 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3526 8 9, g32p_row03_traceSegment_032_3526_0008, g32p_row03_traceSegment_032_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 3510 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3510 16 17, g32p_row03_traceSegment_032_3510_0016, g32p_row03_traceSegment_032_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3543 8 9, g32p_row03_traceSegment_032_3543_0008, g32p_row03_traceSegment_032_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3560 8 9, g32p_row03_traceSegment_032_3560_0008, g32p_row03_traceSegment_032_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3543 17 17, g32p_row03_traceSegment_032_3543_0017, g32p_row03_traceSegment_032_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 3510 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3510 33 34, g32p_row03_traceSegment_032_3510_0033, g32p_row03_traceSegment_032_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3577 8 9, g32p_row03_traceSegment_032_3577_0008, g32p_row03_traceSegment_032_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3594 8 9, g32p_row03_traceSegment_032_3594_0008, g32p_row03_traceSegment_032_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3577 17 17, g32p_row03_traceSegment_032_3577_0017, g32p_row03_traceSegment_032_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3611 8 9, g32p_row03_traceSegment_032_3611_0008, g32p_row03_traceSegment_032_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3628 8 9, g32p_row03_traceSegment_032_3628_0008, g32p_row03_traceSegment_032_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3611 17 17, g32p_row03_traceSegment_032_3611_0017, g32p_row03_traceSegment_032_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3577 34 34, g32p_row03_traceSegment_032_3577_0034, g32p_row03_traceSegment_032_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 3510 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3510 67 68, g32p_row03_traceSegment_032_3510_0067, g32p_row03_traceSegment_032_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3661 8 9, g32p_row03_traceSegment_032_3661_0008, g32p_row03_traceSegment_032_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3645 16 17, g32p_row03_traceSegment_032_3645_0016, g32p_row03_traceSegment_032_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3678 8 9, g32p_row03_traceSegment_032_3678_0008, g32p_row03_traceSegment_032_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3695 8 9, g32p_row03_traceSegment_032_3695_0008, g32p_row03_traceSegment_032_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3678 17 17, g32p_row03_traceSegment_032_3678_0017, g32p_row03_traceSegment_032_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3645 33 34, g32p_row03_traceSegment_032_3645_0033, g32p_row03_traceSegment_032_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3712 8 9, g32p_row03_traceSegment_032_3712_0008, g32p_row03_traceSegment_032_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3729 8 9, g32p_row03_traceSegment_032_3729_0008, g32p_row03_traceSegment_032_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3712 17 17, g32p_row03_traceSegment_032_3712_0017, g32p_row03_traceSegment_032_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3746 8 9, g32p_row03_traceSegment_032_3746_0008, g32p_row03_traceSegment_032_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3763 8 9, g32p_row03_traceSegment_032_3763_0008, g32p_row03_traceSegment_032_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3746 17 17, g32p_row03_traceSegment_032_3746_0017, g32p_row03_traceSegment_032_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3712 34 34, g32p_row03_traceSegment_032_3712_0034, g32p_row03_traceSegment_032_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3645 67 68, g32p_row03_traceSegment_032_3645_0067, g32p_row03_traceSegment_032_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 3510 270 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3510 135 135, g32p_row03_traceSegment_032_3510_0135, g32p_row03_traceSegment_032_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_032 3240 540 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3240 270 270, g32p_row03_traceSegment_032_3240_0270, g32p_row03_traceSegment_032_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3796 8 9, g32p_row03_traceSegment_032_3796_0008, g32p_row03_traceSegment_032_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3780 16 17, g32p_row03_traceSegment_032_3780_0016, g32p_row03_traceSegment_032_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3813 8 9, g32p_row03_traceSegment_032_3813_0008, g32p_row03_traceSegment_032_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3830 8 9, g32p_row03_traceSegment_032_3830_0008, g32p_row03_traceSegment_032_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3813 17 17, g32p_row03_traceSegment_032_3813_0017, g32p_row03_traceSegment_032_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3780 33 34, g32p_row03_traceSegment_032_3780_0033, g32p_row03_traceSegment_032_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3847 8 9, g32p_row03_traceSegment_032_3847_0008, g32p_row03_traceSegment_032_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3864 8 9, g32p_row03_traceSegment_032_3864_0008, g32p_row03_traceSegment_032_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3847 17 17, g32p_row03_traceSegment_032_3847_0017, g32p_row03_traceSegment_032_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3881 8 9, g32p_row03_traceSegment_032_3881_0008, g32p_row03_traceSegment_032_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3898 8 9, g32p_row03_traceSegment_032_3898_0008, g32p_row03_traceSegment_032_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3881 17 17, g32p_row03_traceSegment_032_3881_0017, g32p_row03_traceSegment_032_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3847 34 34, g32p_row03_traceSegment_032_3847_0034, g32p_row03_traceSegment_032_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3780 67 68, g32p_row03_traceSegment_032_3780_0067, g32p_row03_traceSegment_032_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3931 8 9, g32p_row03_traceSegment_032_3931_0008, g32p_row03_traceSegment_032_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3915 16 17, g32p_row03_traceSegment_032_3915_0016, g32p_row03_traceSegment_032_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3948 8 9, g32p_row03_traceSegment_032_3948_0008, g32p_row03_traceSegment_032_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3965 8 9, g32p_row03_traceSegment_032_3965_0008, g32p_row03_traceSegment_032_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3948 17 17, g32p_row03_traceSegment_032_3948_0017, g32p_row03_traceSegment_032_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3915 33 34, g32p_row03_traceSegment_032_3915_0033, g32p_row03_traceSegment_032_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3982 8 9, g32p_row03_traceSegment_032_3982_0008, g32p_row03_traceSegment_032_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3999 8 9, g32p_row03_traceSegment_032_3999_0008, g32p_row03_traceSegment_032_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3982 17 17, g32p_row03_traceSegment_032_3982_0017, g32p_row03_traceSegment_032_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4016 8 9, g32p_row03_traceSegment_032_4016_0008, g32p_row03_traceSegment_032_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4033 8 9, g32p_row03_traceSegment_032_4033_0008, g32p_row03_traceSegment_032_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4016 17 17, g32p_row03_traceSegment_032_4016_0017, g32p_row03_traceSegment_032_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3982 34 34, g32p_row03_traceSegment_032_3982_0034, g32p_row03_traceSegment_032_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3915 67 68, g32p_row03_traceSegment_032_3915_0067, g32p_row03_traceSegment_032_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3780 135 135, g32p_row03_traceSegment_032_3780_0135, g32p_row03_traceSegment_032_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4066 8 9, g32p_row03_traceSegment_032_4066_0008, g32p_row03_traceSegment_032_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4050 16 17, g32p_row03_traceSegment_032_4050_0016, g32p_row03_traceSegment_032_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4083 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4091 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4083 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4083 8 9, g32p_row03_traceSegment_032_4083_0008, g32p_row03_traceSegment_032_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4100 8 9, g32p_row03_traceSegment_032_4100_0008, g32p_row03_traceSegment_032_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 4083 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4083 17 17, g32p_row03_traceSegment_032_4083_0017, g32p_row03_traceSegment_032_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 4050 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4050 33 34, g32p_row03_traceSegment_032_4050_0033, g32p_row03_traceSegment_032_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4117 8 9, g32p_row03_traceSegment_032_4117_0008, g32p_row03_traceSegment_032_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4134 8 9, g32p_row03_traceSegment_032_4134_0008, g32p_row03_traceSegment_032_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4117 17 17, g32p_row03_traceSegment_032_4117_0017, g32p_row03_traceSegment_032_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4151 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4151 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4151 8 9, g32p_row03_traceSegment_032_4151_0008, g32p_row03_traceSegment_032_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4176 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4168 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4168 8 9, g32p_row03_traceSegment_032_4168_0008, g32p_row03_traceSegment_032_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 4151 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4151 17 17, g32p_row03_traceSegment_032_4151_0017, g32p_row03_traceSegment_032_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 4117 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4117 34 34, g32p_row03_traceSegment_032_4117_0034, g32p_row03_traceSegment_032_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 4050 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4050 67 68, g32p_row03_traceSegment_032_4050_0067, g32p_row03_traceSegment_032_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_032 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4201 8 9, g32p_row03_traceSegment_032_4201_0008, g32p_row03_traceSegment_032_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_032 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4185 16 17, g32p_row03_traceSegment_032_4185_0016, g32p_row03_traceSegment_032_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4218 8 9, g32p_row03_traceSegment_032_4218_0008, g32p_row03_traceSegment_032_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4235 8 9, g32p_row03_traceSegment_032_4235_0008, g32p_row03_traceSegment_032_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4218 17 17, g32p_row03_traceSegment_032_4218_0017, g32p_row03_traceSegment_032_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_032 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4185 33 34, g32p_row03_traceSegment_032_4185_0033, g32p_row03_traceSegment_032_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4252 8 9, g32p_row03_traceSegment_032_4252_0008, g32p_row03_traceSegment_032_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4269 8 9, g32p_row03_traceSegment_032_4269_0008, g32p_row03_traceSegment_032_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4252 17 17, g32p_row03_traceSegment_032_4252_0017, g32p_row03_traceSegment_032_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4286 8 9, g32p_row03_traceSegment_032_4286_0008, g32p_row03_traceSegment_032_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_032 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_032 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_032_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_032 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4303 8 9, g32p_row03_traceSegment_032_4303_0008, g32p_row03_traceSegment_032_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_032 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4286 17 17, g32p_row03_traceSegment_032_4286_0017, g32p_row03_traceSegment_032_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_032 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4252 34 34, g32p_row03_traceSegment_032_4252_0034, g32p_row03_traceSegment_032_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_032 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4185 67 68, g32p_row03_traceSegment_032_4185_0067, g32p_row03_traceSegment_032_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_032_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_032 4050 270 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 4050 135 135, g32p_row03_traceSegment_032_4050_0135, g32p_row03_traceSegment_032_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_032 3780 540 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3780 270 270, g32p_row03_traceSegment_032_3780_0270, g32p_row03_traceSegment_032_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_032_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_032 3240 1080 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 3240 540 540, g32p_row03_traceSegment_032_3240_0540, g32p_row03_traceSegment_032_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_032_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_032 2160 2160 = [0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 2160 1080 1080, g32p_row03_traceSegment_032_2160_1080, g32p_row03_traceSegment_032_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_032_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_032 0 4320 = [0, 0, 0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_032 0 2160 2160, g32p_row03_traceSegment_032_0000_2160, g32p_row03_traceSegment_032_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 32 = [0, 0, 0, 0, 40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_032_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_034_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 0 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 16 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 24 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 16 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 16 8 9, g32p_row03_traceSegment_034_0016_0008, g32p_row03_traceSegment_034_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 0 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 0 16 17, g32p_row03_traceSegment_034_0000_0016, g32p_row03_traceSegment_034_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 33 8 9, g32p_row03_traceSegment_034_0033_0008, g32p_row03_traceSegment_034_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 58 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 50 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 50 8 9, g32p_row03_traceSegment_034_0050_0008, g32p_row03_traceSegment_034_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 33 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 33 17 17, g32p_row03_traceSegment_034_0033_0017, g32p_row03_traceSegment_034_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 0 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 0 33 34, g32p_row03_traceSegment_034_0000_0033, g32p_row03_traceSegment_034_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 67 8 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 75 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 67 17 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 67 8 9, g32p_row03_traceSegment_034_0067_0008, g32p_row03_traceSegment_034_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 84 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 92 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 84 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 84 8 9, g32p_row03_traceSegment_034_0084_0008, g32p_row03_traceSegment_034_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 67 34 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 67 17 17, g32p_row03_traceSegment_034_0067_0017, g32p_row03_traceSegment_034_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 101 8 9, g32p_row03_traceSegment_034_0101_0008, g32p_row03_traceSegment_034_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 118 8 9, g32p_row03_traceSegment_034_0118_0008, g32p_row03_traceSegment_034_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 101 17 17, g32p_row03_traceSegment_034_0101_0017, g32p_row03_traceSegment_034_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 67 68 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 67 34 34, g32p_row03_traceSegment_034_0067_0034, g32p_row03_traceSegment_034_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 0 135 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 0 67 68, g32p_row03_traceSegment_034_0000_0067, g32p_row03_traceSegment_034_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 159 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 151 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 151 8 9, g32p_row03_traceSegment_034_0151_0008, g32p_row03_traceSegment_034_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 135 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 135 16 17, g32p_row03_traceSegment_034_0135_0016, g32p_row03_traceSegment_034_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 168 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 168 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 168 8 9, g32p_row03_traceSegment_034_0168_0008, g32p_row03_traceSegment_034_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 193 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 185 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 185 8 9, g32p_row03_traceSegment_034_0185_0008, g32p_row03_traceSegment_034_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 168 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 168 17 17, g32p_row03_traceSegment_034_0168_0017, g32p_row03_traceSegment_034_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 135 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 135 33 34, g32p_row03_traceSegment_034_0135_0033, g32p_row03_traceSegment_034_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 202 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 210 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 202 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 202 8 9, g32p_row03_traceSegment_034_0202_0008, g32p_row03_traceSegment_034_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 219 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 227 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 219 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 219 8 9, g32p_row03_traceSegment_034_0219_0008, g32p_row03_traceSegment_034_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 202 34 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 202 17 17, g32p_row03_traceSegment_034_0202_0017, g32p_row03_traceSegment_034_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 236 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 236 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 236 8 9, g32p_row03_traceSegment_034_0236_0008, g32p_row03_traceSegment_034_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 253 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 253 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 253 8 9, g32p_row03_traceSegment_034_0253_0008, g32p_row03_traceSegment_034_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 236 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 236 17 17, g32p_row03_traceSegment_034_0236_0017, g32p_row03_traceSegment_034_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 202 68 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 202 34 34, g32p_row03_traceSegment_034_0202_0034, g32p_row03_traceSegment_034_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 135 135 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 135 67 68, g32p_row03_traceSegment_034_0135_0067, g32p_row03_traceSegment_034_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 0 270 = [0, 0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 0 135 135, g32p_row03_traceSegment_034_0000_0135, g32p_row03_traceSegment_034_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 286 8 9, g32p_row03_traceSegment_034_0286_0008, g32p_row03_traceSegment_034_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 270 16 17, g32p_row03_traceSegment_034_0270_0016, g32p_row03_traceSegment_034_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 303 8 9, g32p_row03_traceSegment_034_0303_0008, g32p_row03_traceSegment_034_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 320 8 9, g32p_row03_traceSegment_034_0320_0008, g32p_row03_traceSegment_034_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 303 17 17, g32p_row03_traceSegment_034_0303_0017, g32p_row03_traceSegment_034_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 270 33 34, g32p_row03_traceSegment_034_0270_0033, g32p_row03_traceSegment_034_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 337 8 9, g32p_row03_traceSegment_034_0337_0008, g32p_row03_traceSegment_034_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 354 8 9, g32p_row03_traceSegment_034_0354_0008, g32p_row03_traceSegment_034_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 337 17 17, g32p_row03_traceSegment_034_0337_0017, g32p_row03_traceSegment_034_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 371 8 9, g32p_row03_traceSegment_034_0371_0008, g32p_row03_traceSegment_034_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 388 8 9, g32p_row03_traceSegment_034_0388_0008, g32p_row03_traceSegment_034_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 371 17 17, g32p_row03_traceSegment_034_0371_0017, g32p_row03_traceSegment_034_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 337 34 34, g32p_row03_traceSegment_034_0337_0034, g32p_row03_traceSegment_034_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 270 67 68, g32p_row03_traceSegment_034_0270_0067, g32p_row03_traceSegment_034_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 421 8 9, g32p_row03_traceSegment_034_0421_0008, g32p_row03_traceSegment_034_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 405 16 17, g32p_row03_traceSegment_034_0405_0016, g32p_row03_traceSegment_034_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 438 8 9, g32p_row03_traceSegment_034_0438_0008, g32p_row03_traceSegment_034_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 455 8 9, g32p_row03_traceSegment_034_0455_0008, g32p_row03_traceSegment_034_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 438 17 17, g32p_row03_traceSegment_034_0438_0017, g32p_row03_traceSegment_034_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 405 33 34, g32p_row03_traceSegment_034_0405_0033, g32p_row03_traceSegment_034_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 480 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 472 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 472 8 9, g32p_row03_traceSegment_034_0472_0008, g32p_row03_traceSegment_034_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 489 8 9, g32p_row03_traceSegment_034_0489_0008, g32p_row03_traceSegment_034_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 472 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 472 17 17, g32p_row03_traceSegment_034_0472_0017, g32p_row03_traceSegment_034_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 506 8 9, g32p_row03_traceSegment_034_0506_0008, g32p_row03_traceSegment_034_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 531 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 523 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 523 8 9, g32p_row03_traceSegment_034_0523_0008, g32p_row03_traceSegment_034_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 506 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 506 17 17, g32p_row03_traceSegment_034_0506_0017, g32p_row03_traceSegment_034_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 472 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 472 34 34, g32p_row03_traceSegment_034_0472_0034, g32p_row03_traceSegment_034_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 405 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 405 67 68, g32p_row03_traceSegment_034_0405_0067, g32p_row03_traceSegment_034_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 270 270 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 270 135 135, g32p_row03_traceSegment_034_0270_0135, g32p_row03_traceSegment_034_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_034 0 540 = [0, 0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 0 270 270, g32p_row03_traceSegment_034_0000_0270, g32p_row03_traceSegment_034_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 540 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 556 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 556 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 556 8 9, g32p_row03_traceSegment_034_0556_0008, g32p_row03_traceSegment_034_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 540 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 540 16 17, g32p_row03_traceSegment_034_0540_0016, g32p_row03_traceSegment_034_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 573 8 9, g32p_row03_traceSegment_034_0573_0008, g32p_row03_traceSegment_034_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 598 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 590 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 590 8 9, g32p_row03_traceSegment_034_0590_0008, g32p_row03_traceSegment_034_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 573 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 573 17 17, g32p_row03_traceSegment_034_0573_0017, g32p_row03_traceSegment_034_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 540 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 540 33 34, g32p_row03_traceSegment_034_0540_0033, g32p_row03_traceSegment_034_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 607 8 9, g32p_row03_traceSegment_034_0607_0008, g32p_row03_traceSegment_034_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 624 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 632 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 624 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 624 8 9, g32p_row03_traceSegment_034_0624_0008, g32p_row03_traceSegment_034_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 607 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 607 17 17, g32p_row03_traceSegment_034_0607_0017, g32p_row03_traceSegment_034_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 641 8 9, g32p_row03_traceSegment_034_0641_0008, g32p_row03_traceSegment_034_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 666 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 658 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 658 8 9, g32p_row03_traceSegment_034_0658_0008, g32p_row03_traceSegment_034_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 641 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 641 17 17, g32p_row03_traceSegment_034_0641_0017, g32p_row03_traceSegment_034_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 607 68 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 607 34 34, g32p_row03_traceSegment_034_0607_0034, g32p_row03_traceSegment_034_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 540 135 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 540 67 68, g32p_row03_traceSegment_034_0540_0067, g32p_row03_traceSegment_034_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 675 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 691 8 9, g32p_row03_traceSegment_034_0691_0008, g32p_row03_traceSegment_034_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 675 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 675 16 17, g32p_row03_traceSegment_034_0675_0016, g32p_row03_traceSegment_034_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 716 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 708 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 708 8 9, g32p_row03_traceSegment_034_0708_0008, g32p_row03_traceSegment_034_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 725 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 733 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 725 17 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 725 8 9, g32p_row03_traceSegment_034_0725_0008, g32p_row03_traceSegment_034_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 708 34 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 708 17 17, g32p_row03_traceSegment_034_0708_0017, g32p_row03_traceSegment_034_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 675 67 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 675 33 34, g32p_row03_traceSegment_034_0675_0033, g32p_row03_traceSegment_034_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 742 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 742 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 742 8 9, g32p_row03_traceSegment_034_0742_0008, g32p_row03_traceSegment_034_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 767 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 759 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 759 8 9, g32p_row03_traceSegment_034_0759_0008, g32p_row03_traceSegment_034_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 742 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 742 17 17, g32p_row03_traceSegment_034_0742_0017, g32p_row03_traceSegment_034_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 776 8 9, g32p_row03_traceSegment_034_0776_0008, g32p_row03_traceSegment_034_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 793 8 9, g32p_row03_traceSegment_034_0793_0008, g32p_row03_traceSegment_034_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 776 17 17, g32p_row03_traceSegment_034_0776_0017, g32p_row03_traceSegment_034_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 742 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 742 34 34, g32p_row03_traceSegment_034_0742_0034, g32p_row03_traceSegment_034_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 675 135 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 675 67 68, g32p_row03_traceSegment_034_0675_0067, g32p_row03_traceSegment_034_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 540 270 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 540 135 135, g32p_row03_traceSegment_034_0540_0135, g32p_row03_traceSegment_034_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 826 8 9, g32p_row03_traceSegment_034_0826_0008, g32p_row03_traceSegment_034_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 810 16 17, g32p_row03_traceSegment_034_0810_0016, g32p_row03_traceSegment_034_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 843 8 9, g32p_row03_traceSegment_034_0843_0008, g32p_row03_traceSegment_034_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 860 8 9, g32p_row03_traceSegment_034_0860_0008, g32p_row03_traceSegment_034_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 843 17 17, g32p_row03_traceSegment_034_0843_0017, g32p_row03_traceSegment_034_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 810 33 34, g32p_row03_traceSegment_034_0810_0033, g32p_row03_traceSegment_034_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 877 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 877 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 877 8 9, g32p_row03_traceSegment_034_0877_0008, g32p_row03_traceSegment_034_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 894 8 9, g32p_row03_traceSegment_034_0894_0008, g32p_row03_traceSegment_034_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 877 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 877 17 17, g32p_row03_traceSegment_034_0877_0017, g32p_row03_traceSegment_034_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 911 8 9, g32p_row03_traceSegment_034_0911_0008, g32p_row03_traceSegment_034_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 928 8 9, g32p_row03_traceSegment_034_0928_0008, g32p_row03_traceSegment_034_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 911 17 17, g32p_row03_traceSegment_034_0911_0017, g32p_row03_traceSegment_034_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 877 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 877 34 34, g32p_row03_traceSegment_034_0877_0034, g32p_row03_traceSegment_034_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 810 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 810 67 68, g32p_row03_traceSegment_034_0810_0067, g32p_row03_traceSegment_034_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 961 8 9, g32p_row03_traceSegment_034_0961_0008, g32p_row03_traceSegment_034_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 945 16 17, g32p_row03_traceSegment_034_0945_0016, g32p_row03_traceSegment_034_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 978 8 9, g32p_row03_traceSegment_034_0978_0008, g32p_row03_traceSegment_034_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 995 8 9, g32p_row03_traceSegment_034_0995_0008, g32p_row03_traceSegment_034_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 978 17 17, g32p_row03_traceSegment_034_0978_0017, g32p_row03_traceSegment_034_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 945 33 34, g32p_row03_traceSegment_034_0945_0033, g32p_row03_traceSegment_034_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1012 8 9, g32p_row03_traceSegment_034_1012_0008, g32p_row03_traceSegment_034_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1029 8 9, g32p_row03_traceSegment_034_1029_0008, g32p_row03_traceSegment_034_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1012 17 17, g32p_row03_traceSegment_034_1012_0017, g32p_row03_traceSegment_034_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1046 8 9, g32p_row03_traceSegment_034_1046_0008, g32p_row03_traceSegment_034_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1071 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1063 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1063 8 9, g32p_row03_traceSegment_034_1063_0008, g32p_row03_traceSegment_034_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1046 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1046 17 17, g32p_row03_traceSegment_034_1046_0017, g32p_row03_traceSegment_034_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 1012 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1012 34 34, g32p_row03_traceSegment_034_1012_0034, g32p_row03_traceSegment_034_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 945 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 945 67 68, g32p_row03_traceSegment_034_0945_0067, g32p_row03_traceSegment_034_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 810 270 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 810 135 135, g32p_row03_traceSegment_034_0810_0135, g32p_row03_traceSegment_034_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_034 540 540 = [0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 540 270 270, g32p_row03_traceSegment_034_0540_0270, g32p_row03_traceSegment_034_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_034 0 1080 = [0, 0, 0, 0, 39] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 0 540 540, g32p_row03_traceSegment_034_0000_0540, g32p_row03_traceSegment_034_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1096 8 9, g32p_row03_traceSegment_034_1096_0008, g32p_row03_traceSegment_034_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1080 16 17, g32p_row03_traceSegment_034_1080_0016, g32p_row03_traceSegment_034_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1113 8 9, g32p_row03_traceSegment_034_1113_0008, g32p_row03_traceSegment_034_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1130 8 9, g32p_row03_traceSegment_034_1130_0008, g32p_row03_traceSegment_034_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1113 17 17, g32p_row03_traceSegment_034_1113_0017, g32p_row03_traceSegment_034_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1080 33 34, g32p_row03_traceSegment_034_1080_0033, g32p_row03_traceSegment_034_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1147 8 9, g32p_row03_traceSegment_034_1147_0008, g32p_row03_traceSegment_034_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1164 8 9, g32p_row03_traceSegment_034_1164_0008, g32p_row03_traceSegment_034_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1147 17 17, g32p_row03_traceSegment_034_1147_0017, g32p_row03_traceSegment_034_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1181 8 9, g32p_row03_traceSegment_034_1181_0008, g32p_row03_traceSegment_034_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1198 8 9, g32p_row03_traceSegment_034_1198_0008, g32p_row03_traceSegment_034_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1181 17 17, g32p_row03_traceSegment_034_1181_0017, g32p_row03_traceSegment_034_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1147 34 34, g32p_row03_traceSegment_034_1147_0034, g32p_row03_traceSegment_034_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1080 67 68, g32p_row03_traceSegment_034_1080_0067, g32p_row03_traceSegment_034_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 1215 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1231 8 9, g32p_row03_traceSegment_034_1231_0008, g32p_row03_traceSegment_034_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 1215 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1215 16 17, g32p_row03_traceSegment_034_1215_0016, g32p_row03_traceSegment_034_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1248 8 9, g32p_row03_traceSegment_034_1248_0008, g32p_row03_traceSegment_034_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1273 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1265 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1265 8 9, g32p_row03_traceSegment_034_1265_0008, g32p_row03_traceSegment_034_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1248 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1248 17 17, g32p_row03_traceSegment_034_1248_0017, g32p_row03_traceSegment_034_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 1215 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1215 33 34, g32p_row03_traceSegment_034_1215_0033, g32p_row03_traceSegment_034_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1290 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1282 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1282 8 9, g32p_row03_traceSegment_034_1282_0008, g32p_row03_traceSegment_034_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1299 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1299 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1299 8 9, g32p_row03_traceSegment_034_1299_0008, g32p_row03_traceSegment_034_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1282 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1282 17 17, g32p_row03_traceSegment_034_1282_0017, g32p_row03_traceSegment_034_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1316 8 9, g32p_row03_traceSegment_034_1316_0008, g32p_row03_traceSegment_034_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1333 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1333 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1333 8 9, g32p_row03_traceSegment_034_1333_0008, g32p_row03_traceSegment_034_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1316 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1316 17 17, g32p_row03_traceSegment_034_1316_0017, g32p_row03_traceSegment_034_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 1282 68 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1282 34 34, g32p_row03_traceSegment_034_1282_0034, g32p_row03_traceSegment_034_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 1215 135 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1215 67 68, g32p_row03_traceSegment_034_1215_0067, g32p_row03_traceSegment_034_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 1080 270 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1080 135 135, g32p_row03_traceSegment_034_1080_0135, g32p_row03_traceSegment_034_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 1350 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1366 8 9, g32p_row03_traceSegment_034_1366_0008, g32p_row03_traceSegment_034_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 1350 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1350 16 17, g32p_row03_traceSegment_034_1350_0016, g32p_row03_traceSegment_034_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1383 8 9, g32p_row03_traceSegment_034_1383_0008, g32p_row03_traceSegment_034_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1400 8 9, g32p_row03_traceSegment_034_1400_0008, g32p_row03_traceSegment_034_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1383 17 17, g32p_row03_traceSegment_034_1383_0017, g32p_row03_traceSegment_034_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 1350 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1350 33 34, g32p_row03_traceSegment_034_1350_0033, g32p_row03_traceSegment_034_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1425 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1417 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1417 8 9, g32p_row03_traceSegment_034_1417_0008, g32p_row03_traceSegment_034_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1442 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1434 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1434 8 9, g32p_row03_traceSegment_034_1434_0008, g32p_row03_traceSegment_034_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1417 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1417 17 17, g32p_row03_traceSegment_034_1417_0017, g32p_row03_traceSegment_034_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1459 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1451 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1451 8 9, g32p_row03_traceSegment_034_1451_0008, g32p_row03_traceSegment_034_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1468 8 9, g32p_row03_traceSegment_034_1468_0008, g32p_row03_traceSegment_034_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1451 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1451 17 17, g32p_row03_traceSegment_034_1451_0017, g32p_row03_traceSegment_034_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 1417 68 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1417 34 34, g32p_row03_traceSegment_034_1417_0034, g32p_row03_traceSegment_034_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 1350 135 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1350 67 68, g32p_row03_traceSegment_034_1350_0067, g32p_row03_traceSegment_034_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 1485 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1501 8 9, g32p_row03_traceSegment_034_1501_0008, g32p_row03_traceSegment_034_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 1485 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1485 16 17, g32p_row03_traceSegment_034_1485_0016, g32p_row03_traceSegment_034_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1526 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1518 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1518 8 9, g32p_row03_traceSegment_034_1518_0008, g32p_row03_traceSegment_034_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1535 8 9, g32p_row03_traceSegment_034_1535_0008, g32p_row03_traceSegment_034_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1518 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1518 17 17, g32p_row03_traceSegment_034_1518_0017, g32p_row03_traceSegment_034_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 1485 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1485 33 34, g32p_row03_traceSegment_034_1485_0033, g32p_row03_traceSegment_034_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1552 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1552 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1552 8 9, g32p_row03_traceSegment_034_1552_0008, g32p_row03_traceSegment_034_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1569 8 9, g32p_row03_traceSegment_034_1569_0008, g32p_row03_traceSegment_034_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1552 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1552 17 17, g32p_row03_traceSegment_034_1552_0017, g32p_row03_traceSegment_034_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1586 8 9, g32p_row03_traceSegment_034_1586_0008, g32p_row03_traceSegment_034_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1603 8 9, g32p_row03_traceSegment_034_1603_0008, g32p_row03_traceSegment_034_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1586 17 17, g32p_row03_traceSegment_034_1586_0017, g32p_row03_traceSegment_034_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 1552 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1552 34 34, g32p_row03_traceSegment_034_1552_0034, g32p_row03_traceSegment_034_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 1485 135 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1485 67 68, g32p_row03_traceSegment_034_1485_0067, g32p_row03_traceSegment_034_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 1350 270 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1350 135 135, g32p_row03_traceSegment_034_1350_0135, g32p_row03_traceSegment_034_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_034 1080 540 = [0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1080 270 270, g32p_row03_traceSegment_034_1080_0270, g32p_row03_traceSegment_034_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1644 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1636 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1636 8 9, g32p_row03_traceSegment_034_1636_0008, g32p_row03_traceSegment_034_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 1620 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1620 16 17, g32p_row03_traceSegment_034_1620_0016, g32p_row03_traceSegment_034_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1653 8 9, g32p_row03_traceSegment_034_1653_0008, g32p_row03_traceSegment_034_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1670 8 9, g32p_row03_traceSegment_034_1670_0008, g32p_row03_traceSegment_034_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1653 17 17, g32p_row03_traceSegment_034_1653_0017, g32p_row03_traceSegment_034_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 1620 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1620 33 34, g32p_row03_traceSegment_034_1620_0033, g32p_row03_traceSegment_034_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1687 8 9, g32p_row03_traceSegment_034_1687_0008, g32p_row03_traceSegment_034_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1704 8 9, g32p_row03_traceSegment_034_1704_0008, g32p_row03_traceSegment_034_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1687 17 17, g32p_row03_traceSegment_034_1687_0017, g32p_row03_traceSegment_034_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1729 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1721 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1721 8 9, g32p_row03_traceSegment_034_1721_0008, g32p_row03_traceSegment_034_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1738 8 9, g32p_row03_traceSegment_034_1738_0008, g32p_row03_traceSegment_034_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1721 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1721 17 17, g32p_row03_traceSegment_034_1721_0017, g32p_row03_traceSegment_034_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 1687 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1687 34 34, g32p_row03_traceSegment_034_1687_0034, g32p_row03_traceSegment_034_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 1620 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1620 67 68, g32p_row03_traceSegment_034_1620_0067, g32p_row03_traceSegment_034_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1779 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1771 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1771 8 9, g32p_row03_traceSegment_034_1771_0008, g32p_row03_traceSegment_034_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 1755 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1755 16 17, g32p_row03_traceSegment_034_1755_0016, g32p_row03_traceSegment_034_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1796 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1788 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1788 8 9, g32p_row03_traceSegment_034_1788_0008, g32p_row03_traceSegment_034_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1805 8 9, g32p_row03_traceSegment_034_1805_0008, g32p_row03_traceSegment_034_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1788 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1788 17 17, g32p_row03_traceSegment_034_1788_0017, g32p_row03_traceSegment_034_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 1755 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1755 33 34, g32p_row03_traceSegment_034_1755_0033, g32p_row03_traceSegment_034_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1822 8 9, g32p_row03_traceSegment_034_1822_0008, g32p_row03_traceSegment_034_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1839 8 9, g32p_row03_traceSegment_034_1839_0008, g32p_row03_traceSegment_034_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1822 17 17, g32p_row03_traceSegment_034_1822_0017, g32p_row03_traceSegment_034_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1856 8 9, g32p_row03_traceSegment_034_1856_0008, g32p_row03_traceSegment_034_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1873 8 9, g32p_row03_traceSegment_034_1873_0008, g32p_row03_traceSegment_034_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1856 17 17, g32p_row03_traceSegment_034_1856_0017, g32p_row03_traceSegment_034_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1822 34 34, g32p_row03_traceSegment_034_1822_0034, g32p_row03_traceSegment_034_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 1755 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1755 67 68, g32p_row03_traceSegment_034_1755_0067, g32p_row03_traceSegment_034_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 1620 270 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1620 135 135, g32p_row03_traceSegment_034_1620_0135, g32p_row03_traceSegment_034_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1906 8 9, g32p_row03_traceSegment_034_1906_0008, g32p_row03_traceSegment_034_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1890 16 17, g32p_row03_traceSegment_034_1890_0016, g32p_row03_traceSegment_034_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1923 8 9, g32p_row03_traceSegment_034_1923_0008, g32p_row03_traceSegment_034_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1940 8 9, g32p_row03_traceSegment_034_1940_0008, g32p_row03_traceSegment_034_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1923 17 17, g32p_row03_traceSegment_034_1923_0017, g32p_row03_traceSegment_034_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1890 33 34, g32p_row03_traceSegment_034_1890_0033, g32p_row03_traceSegment_034_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1957 8 9, g32p_row03_traceSegment_034_1957_0008, g32p_row03_traceSegment_034_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1974 8 9, g32p_row03_traceSegment_034_1974_0008, g32p_row03_traceSegment_034_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1957 17 17, g32p_row03_traceSegment_034_1957_0017, g32p_row03_traceSegment_034_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 1999 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 1991 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1991 8 9, g32p_row03_traceSegment_034_1991_0008, g32p_row03_traceSegment_034_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2008 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2008 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2008 8 9, g32p_row03_traceSegment_034_2008_0008, g32p_row03_traceSegment_034_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 1991 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1991 17 17, g32p_row03_traceSegment_034_1991_0017, g32p_row03_traceSegment_034_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 1957 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1957 34 34, g32p_row03_traceSegment_034_1957_0034, g32p_row03_traceSegment_034_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 1890 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1890 67 68, g32p_row03_traceSegment_034_1890_0067, g32p_row03_traceSegment_034_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2041 8 9, g32p_row03_traceSegment_034_2041_0008, g32p_row03_traceSegment_034_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2025 16 17, g32p_row03_traceSegment_034_2025_0016, g32p_row03_traceSegment_034_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2058 8 9, g32p_row03_traceSegment_034_2058_0008, g32p_row03_traceSegment_034_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2075 8 9, g32p_row03_traceSegment_034_2075_0008, g32p_row03_traceSegment_034_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2058 17 17, g32p_row03_traceSegment_034_2058_0017, g32p_row03_traceSegment_034_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2025 33 34, g32p_row03_traceSegment_034_2025_0033, g32p_row03_traceSegment_034_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2092 8 9, g32p_row03_traceSegment_034_2092_0008, g32p_row03_traceSegment_034_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2109 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2109 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2109 8 9, g32p_row03_traceSegment_034_2109_0008, g32p_row03_traceSegment_034_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2092 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2092 17 17, g32p_row03_traceSegment_034_2092_0017, g32p_row03_traceSegment_034_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2126 8 9, g32p_row03_traceSegment_034_2126_0008, g32p_row03_traceSegment_034_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2143 8 9, g32p_row03_traceSegment_034_2143_0008, g32p_row03_traceSegment_034_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2126 17 17, g32p_row03_traceSegment_034_2126_0017, g32p_row03_traceSegment_034_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 2092 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2092 34 34, g32p_row03_traceSegment_034_2092_0034, g32p_row03_traceSegment_034_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 2025 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2025 67 68, g32p_row03_traceSegment_034_2025_0067, g32p_row03_traceSegment_034_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 1890 270 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1890 135 135, g32p_row03_traceSegment_034_1890_0135, g32p_row03_traceSegment_034_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_034 1620 540 = [0, 1, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1620 270 270, g32p_row03_traceSegment_034_1620_0270, g32p_row03_traceSegment_034_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_034_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_034 1080 1080 = [0, 1, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 1080 540 540, g32p_row03_traceSegment_034_1080_0540, g32p_row03_traceSegment_034_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_034 0 2160 = [0, 1, 0, 0, 60] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 0 1080 1080, g32p_row03_traceSegment_034_0000_1080, g32p_row03_traceSegment_034_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2184 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2176 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2176 8 9, g32p_row03_traceSegment_034_2176_0008, g32p_row03_traceSegment_034_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 2160 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2160 16 17, g32p_row03_traceSegment_034_2160_0016, g32p_row03_traceSegment_034_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2201 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2193 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2193 8 9, g32p_row03_traceSegment_034_2193_0008, g32p_row03_traceSegment_034_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2210 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2210 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2210 8 9, g32p_row03_traceSegment_034_2210_0008, g32p_row03_traceSegment_034_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2193 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2193 17 17, g32p_row03_traceSegment_034_2193_0017, g32p_row03_traceSegment_034_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 2160 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2160 33 34, g32p_row03_traceSegment_034_2160_0033, g32p_row03_traceSegment_034_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2227 8 9, g32p_row03_traceSegment_034_2227_0008, g32p_row03_traceSegment_034_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2244 8 9, g32p_row03_traceSegment_034_2244_0008, g32p_row03_traceSegment_034_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2227 17 17, g32p_row03_traceSegment_034_2227_0017, g32p_row03_traceSegment_034_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2261 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2261 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2261 8 9, g32p_row03_traceSegment_034_2261_0008, g32p_row03_traceSegment_034_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2278 8 9, g32p_row03_traceSegment_034_2278_0008, g32p_row03_traceSegment_034_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2261 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2261 17 17, g32p_row03_traceSegment_034_2261_0017, g32p_row03_traceSegment_034_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 2227 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2227 34 34, g32p_row03_traceSegment_034_2227_0034, g32p_row03_traceSegment_034_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 2160 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2160 67 68, g32p_row03_traceSegment_034_2160_0067, g32p_row03_traceSegment_034_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 2295 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2311 8 9, g32p_row03_traceSegment_034_2311_0008, g32p_row03_traceSegment_034_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 2295 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2295 16 17, g32p_row03_traceSegment_034_2295_0016, g32p_row03_traceSegment_034_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2328 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2328 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2328 8 9, g32p_row03_traceSegment_034_2328_0008, g32p_row03_traceSegment_034_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2345 8 9, g32p_row03_traceSegment_034_2345_0008, g32p_row03_traceSegment_034_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2328 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2328 17 17, g32p_row03_traceSegment_034_2328_0017, g32p_row03_traceSegment_034_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 2295 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2295 33 34, g32p_row03_traceSegment_034_2295_0033, g32p_row03_traceSegment_034_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2370 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2362 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2362 8 9, g32p_row03_traceSegment_034_2362_0008, g32p_row03_traceSegment_034_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2379 8 9, g32p_row03_traceSegment_034_2379_0008, g32p_row03_traceSegment_034_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2362 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2362 17 17, g32p_row03_traceSegment_034_2362_0017, g32p_row03_traceSegment_034_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2396 8 9, g32p_row03_traceSegment_034_2396_0008, g32p_row03_traceSegment_034_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2413 8 9, g32p_row03_traceSegment_034_2413_0008, g32p_row03_traceSegment_034_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2396 17 17, g32p_row03_traceSegment_034_2396_0017, g32p_row03_traceSegment_034_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 2362 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2362 34 34, g32p_row03_traceSegment_034_2362_0034, g32p_row03_traceSegment_034_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 2295 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2295 67 68, g32p_row03_traceSegment_034_2295_0067, g32p_row03_traceSegment_034_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 2160 270 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2160 135 135, g32p_row03_traceSegment_034_2160_0135, g32p_row03_traceSegment_034_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2446 8 9, g32p_row03_traceSegment_034_2446_0008, g32p_row03_traceSegment_034_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2430 16 17, g32p_row03_traceSegment_034_2430_0016, g32p_row03_traceSegment_034_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2471 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2463 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2463 8 9, g32p_row03_traceSegment_034_2463_0008, g32p_row03_traceSegment_034_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2480 8 9, g32p_row03_traceSegment_034_2480_0008, g32p_row03_traceSegment_034_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2463 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2463 17 17, g32p_row03_traceSegment_034_2463_0017, g32p_row03_traceSegment_034_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 2430 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2430 33 34, g32p_row03_traceSegment_034_2430_0033, g32p_row03_traceSegment_034_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2497 8 9, g32p_row03_traceSegment_034_2497_0008, g32p_row03_traceSegment_034_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2514 8 9, g32p_row03_traceSegment_034_2514_0008, g32p_row03_traceSegment_034_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2497 17 17, g32p_row03_traceSegment_034_2497_0017, g32p_row03_traceSegment_034_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2539 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2531 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2531 8 9, g32p_row03_traceSegment_034_2531_0008, g32p_row03_traceSegment_034_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2548 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2548 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2548 8 9, g32p_row03_traceSegment_034_2548_0008, g32p_row03_traceSegment_034_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2531 34 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2531 17 17, g32p_row03_traceSegment_034_2531_0017, g32p_row03_traceSegment_034_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 2497 68 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2497 34 34, g32p_row03_traceSegment_034_2497_0034, g32p_row03_traceSegment_034_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 2430 135 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2430 67 68, g32p_row03_traceSegment_034_2430_0067, g32p_row03_traceSegment_034_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 2565 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2581 8 9, g32p_row03_traceSegment_034_2581_0008, g32p_row03_traceSegment_034_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 2565 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2565 16 17, g32p_row03_traceSegment_034_2565_0016, g32p_row03_traceSegment_034_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2606 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2598 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2598 8 9, g32p_row03_traceSegment_034_2598_0008, g32p_row03_traceSegment_034_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2615 8 9, g32p_row03_traceSegment_034_2615_0008, g32p_row03_traceSegment_034_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2598 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2598 17 17, g32p_row03_traceSegment_034_2598_0017, g32p_row03_traceSegment_034_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 2565 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2565 33 34, g32p_row03_traceSegment_034_2565_0033, g32p_row03_traceSegment_034_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2632 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2632 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2632 8 9, g32p_row03_traceSegment_034_2632_0008, g32p_row03_traceSegment_034_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2649 8 9, g32p_row03_traceSegment_034_2649_0008, g32p_row03_traceSegment_034_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2632 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2632 17 17, g32p_row03_traceSegment_034_2632_0017, g32p_row03_traceSegment_034_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2666 8 9, g32p_row03_traceSegment_034_2666_0008, g32p_row03_traceSegment_034_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2683 8 9, g32p_row03_traceSegment_034_2683_0008, g32p_row03_traceSegment_034_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2666 17 17, g32p_row03_traceSegment_034_2666_0017, g32p_row03_traceSegment_034_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 2632 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2632 34 34, g32p_row03_traceSegment_034_2632_0034, g32p_row03_traceSegment_034_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 2565 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2565 67 68, g32p_row03_traceSegment_034_2565_0067, g32p_row03_traceSegment_034_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 2430 270 = [0, 5, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2430 135 135, g32p_row03_traceSegment_034_2430_0135, g32p_row03_traceSegment_034_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_034 2160 540 = [0, 12, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2160 270 270, g32p_row03_traceSegment_034_2160_0270, g32p_row03_traceSegment_034_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2716 8 9, g32p_row03_traceSegment_034_2716_0008, g32p_row03_traceSegment_034_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2700 16 17, g32p_row03_traceSegment_034_2700_0016, g32p_row03_traceSegment_034_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2733 8 9, g32p_row03_traceSegment_034_2733_0008, g32p_row03_traceSegment_034_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2750 8 9, g32p_row03_traceSegment_034_2750_0008, g32p_row03_traceSegment_034_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2733 17 17, g32p_row03_traceSegment_034_2733_0017, g32p_row03_traceSegment_034_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2700 33 34, g32p_row03_traceSegment_034_2700_0033, g32p_row03_traceSegment_034_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2767 8 9, g32p_row03_traceSegment_034_2767_0008, g32p_row03_traceSegment_034_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2792 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2784 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2784 8 9, g32p_row03_traceSegment_034_2784_0008, g32p_row03_traceSegment_034_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2767 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2767 17 17, g32p_row03_traceSegment_034_2767_0017, g32p_row03_traceSegment_034_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2801 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2801 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2801 8 9, g32p_row03_traceSegment_034_2801_0008, g32p_row03_traceSegment_034_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2818 8 9, g32p_row03_traceSegment_034_2818_0008, g32p_row03_traceSegment_034_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2801 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2801 17 17, g32p_row03_traceSegment_034_2801_0017, g32p_row03_traceSegment_034_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 2767 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2767 34 34, g32p_row03_traceSegment_034_2767_0034, g32p_row03_traceSegment_034_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 2700 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2700 67 68, g32p_row03_traceSegment_034_2700_0067, g32p_row03_traceSegment_034_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2851 8 9, g32p_row03_traceSegment_034_2851_0008, g32p_row03_traceSegment_034_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2835 16 17, g32p_row03_traceSegment_034_2835_0016, g32p_row03_traceSegment_034_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2868 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2868 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2868 8 9, g32p_row03_traceSegment_034_2868_0008, g32p_row03_traceSegment_034_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2885 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2893 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2885 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2885 8 9, g32p_row03_traceSegment_034_2885_0008, g32p_row03_traceSegment_034_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2868 34 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2868 17 17, g32p_row03_traceSegment_034_2868_0017, g32p_row03_traceSegment_034_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 2835 67 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2835 33 34, g32p_row03_traceSegment_034_2835_0033, g32p_row03_traceSegment_034_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2902 8 9, g32p_row03_traceSegment_034_2902_0008, g32p_row03_traceSegment_034_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2927 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2919 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2919 8 9, g32p_row03_traceSegment_034_2919_0008, g32p_row03_traceSegment_034_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2902 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2902 17 17, g32p_row03_traceSegment_034_2902_0017, g32p_row03_traceSegment_034_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2936 8 9, g32p_row03_traceSegment_034_2936_0008, g32p_row03_traceSegment_034_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2953 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2953 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2953 8 9, g32p_row03_traceSegment_034_2953_0008, g32p_row03_traceSegment_034_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 2936 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2936 17 17, g32p_row03_traceSegment_034_2936_0017, g32p_row03_traceSegment_034_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 2902 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2902 34 34, g32p_row03_traceSegment_034_2902_0034, g32p_row03_traceSegment_034_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 2835 135 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2835 67 68, g32p_row03_traceSegment_034_2835_0067, g32p_row03_traceSegment_034_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 2700 270 = [0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2700 135 135, g32p_row03_traceSegment_034_2700_0135, g32p_row03_traceSegment_034_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2986 8 9, g32p_row03_traceSegment_034_2986_0008, g32p_row03_traceSegment_034_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2970 16 17, g32p_row03_traceSegment_034_2970_0016, g32p_row03_traceSegment_034_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3003 8 9, g32p_row03_traceSegment_034_3003_0008, g32p_row03_traceSegment_034_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3020 8 9, g32p_row03_traceSegment_034_3020_0008, g32p_row03_traceSegment_034_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3003 17 17, g32p_row03_traceSegment_034_3003_0017, g32p_row03_traceSegment_034_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2970 33 34, g32p_row03_traceSegment_034_2970_0033, g32p_row03_traceSegment_034_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3037 8 9, g32p_row03_traceSegment_034_3037_0008, g32p_row03_traceSegment_034_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3054 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3054 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3054 8 9, g32p_row03_traceSegment_034_3054_0008, g32p_row03_traceSegment_034_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3037 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3037 17 17, g32p_row03_traceSegment_034_3037_0017, g32p_row03_traceSegment_034_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3071 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3071 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3071 8 9, g32p_row03_traceSegment_034_3071_0008, g32p_row03_traceSegment_034_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3088 8 9, g32p_row03_traceSegment_034_3088_0008, g32p_row03_traceSegment_034_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3071 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3071 17 17, g32p_row03_traceSegment_034_3071_0017, g32p_row03_traceSegment_034_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 3037 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3037 34 34, g32p_row03_traceSegment_034_3037_0034, g32p_row03_traceSegment_034_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 2970 135 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2970 67 68, g32p_row03_traceSegment_034_2970_0067, g32p_row03_traceSegment_034_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3121 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3129 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3121 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3121 8 9, g32p_row03_traceSegment_034_3121_0008, g32p_row03_traceSegment_034_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 3105 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3105 16 17, g32p_row03_traceSegment_034_3105_0016, g32p_row03_traceSegment_034_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3138 8 9, g32p_row03_traceSegment_034_3138_0008, g32p_row03_traceSegment_034_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3155 8 9, g32p_row03_traceSegment_034_3155_0008, g32p_row03_traceSegment_034_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3138 17 17, g32p_row03_traceSegment_034_3138_0017, g32p_row03_traceSegment_034_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 3105 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3105 33 34, g32p_row03_traceSegment_034_3105_0033, g32p_row03_traceSegment_034_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3172 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3180 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3172 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3172 8 9, g32p_row03_traceSegment_034_3172_0008, g32p_row03_traceSegment_034_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3189 8 9, g32p_row03_traceSegment_034_3189_0008, g32p_row03_traceSegment_034_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3172 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3172 17 17, g32p_row03_traceSegment_034_3172_0017, g32p_row03_traceSegment_034_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3206 8 9, g32p_row03_traceSegment_034_3206_0008, g32p_row03_traceSegment_034_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3223 8 9, g32p_row03_traceSegment_034_3223_0008, g32p_row03_traceSegment_034_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3206 17 17, g32p_row03_traceSegment_034_3206_0017, g32p_row03_traceSegment_034_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 3172 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3172 34 34, g32p_row03_traceSegment_034_3172_0034, g32p_row03_traceSegment_034_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 3105 135 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3105 67 68, g32p_row03_traceSegment_034_3105_0067, g32p_row03_traceSegment_034_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 2970 270 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2970 135 135, g32p_row03_traceSegment_034_2970_0135, g32p_row03_traceSegment_034_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_034 2700 540 = [0, 3, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2700 270 270, g32p_row03_traceSegment_034_2700_0270, g32p_row03_traceSegment_034_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_034 2160 1080 = [0, 15, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2160 540 540, g32p_row03_traceSegment_034_2160_0540, g32p_row03_traceSegment_034_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 3240 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3256 8 9, g32p_row03_traceSegment_034_3256_0008, g32p_row03_traceSegment_034_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 3240 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3240 16 17, g32p_row03_traceSegment_034_3240_0016, g32p_row03_traceSegment_034_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3281 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3273 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3273 8 9, g32p_row03_traceSegment_034_3273_0008, g32p_row03_traceSegment_034_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3298 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3290 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3290 8 9, g32p_row03_traceSegment_034_3290_0008, g32p_row03_traceSegment_034_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3273 34 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3273 17 17, g32p_row03_traceSegment_034_3273_0017, g32p_row03_traceSegment_034_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 3240 67 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3240 33 34, g32p_row03_traceSegment_034_3240_0033, g32p_row03_traceSegment_034_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3315 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3307 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3307 8 9, g32p_row03_traceSegment_034_3307_0008, g32p_row03_traceSegment_034_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3324 8 9, g32p_row03_traceSegment_034_3324_0008, g32p_row03_traceSegment_034_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3307 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3307 17 17, g32p_row03_traceSegment_034_3307_0017, g32p_row03_traceSegment_034_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3341 8 9, g32p_row03_traceSegment_034_3341_0008, g32p_row03_traceSegment_034_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3358 8 9, g32p_row03_traceSegment_034_3358_0008, g32p_row03_traceSegment_034_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3341 17 17, g32p_row03_traceSegment_034_3341_0017, g32p_row03_traceSegment_034_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 3307 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3307 34 34, g32p_row03_traceSegment_034_3307_0034, g32p_row03_traceSegment_034_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 3240 135 = [0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3240 67 68, g32p_row03_traceSegment_034_3240_0067, g32p_row03_traceSegment_034_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 3375 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3391 8 9, g32p_row03_traceSegment_034_3391_0008, g32p_row03_traceSegment_034_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 3375 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3375 16 17, g32p_row03_traceSegment_034_3375_0016, g32p_row03_traceSegment_034_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3408 8 9, g32p_row03_traceSegment_034_3408_0008, g32p_row03_traceSegment_034_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3425 8 9, g32p_row03_traceSegment_034_3425_0008, g32p_row03_traceSegment_034_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3408 17 17, g32p_row03_traceSegment_034_3408_0017, g32p_row03_traceSegment_034_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 3375 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3375 33 34, g32p_row03_traceSegment_034_3375_0033, g32p_row03_traceSegment_034_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3450 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3442 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3442 8 9, g32p_row03_traceSegment_034_3442_0008, g32p_row03_traceSegment_034_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3459 8 9, g32p_row03_traceSegment_034_3459_0008, g32p_row03_traceSegment_034_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3442 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3442 17 17, g32p_row03_traceSegment_034_3442_0017, g32p_row03_traceSegment_034_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3476 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3476 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3476 8 9, g32p_row03_traceSegment_034_3476_0008, g32p_row03_traceSegment_034_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3493 8 9, g32p_row03_traceSegment_034_3493_0008, g32p_row03_traceSegment_034_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3476 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3476 17 17, g32p_row03_traceSegment_034_3476_0017, g32p_row03_traceSegment_034_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 3442 68 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3442 34 34, g32p_row03_traceSegment_034_3442_0034, g32p_row03_traceSegment_034_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 3375 135 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3375 67 68, g32p_row03_traceSegment_034_3375_0067, g32p_row03_traceSegment_034_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 3240 270 = [0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3240 135 135, g32p_row03_traceSegment_034_3240_0135, g32p_row03_traceSegment_034_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3526 8 9, g32p_row03_traceSegment_034_3526_0008, g32p_row03_traceSegment_034_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3510 16 17, g32p_row03_traceSegment_034_3510_0016, g32p_row03_traceSegment_034_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3543 8 9, g32p_row03_traceSegment_034_3543_0008, g32p_row03_traceSegment_034_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3560 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3568 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3560 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3560 8 9, g32p_row03_traceSegment_034_3560_0008, g32p_row03_traceSegment_034_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3543 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3543 17 17, g32p_row03_traceSegment_034_3543_0017, g32p_row03_traceSegment_034_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 3510 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3510 33 34, g32p_row03_traceSegment_034_3510_0033, g32p_row03_traceSegment_034_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3577 8 9, g32p_row03_traceSegment_034_3577_0008, g32p_row03_traceSegment_034_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3594 8 9, g32p_row03_traceSegment_034_3594_0008, g32p_row03_traceSegment_034_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3577 17 17, g32p_row03_traceSegment_034_3577_0017, g32p_row03_traceSegment_034_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3619 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3611 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3611 8 9, g32p_row03_traceSegment_034_3611_0008, g32p_row03_traceSegment_034_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3628 8 9, g32p_row03_traceSegment_034_3628_0008, g32p_row03_traceSegment_034_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3611 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3611 17 17, g32p_row03_traceSegment_034_3611_0017, g32p_row03_traceSegment_034_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 3577 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3577 34 34, g32p_row03_traceSegment_034_3577_0034, g32p_row03_traceSegment_034_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 3510 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3510 67 68, g32p_row03_traceSegment_034_3510_0067, g32p_row03_traceSegment_034_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3669 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3661 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3661 8 9, g32p_row03_traceSegment_034_3661_0008, g32p_row03_traceSegment_034_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 3645 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3645 16 17, g32p_row03_traceSegment_034_3645_0016, g32p_row03_traceSegment_034_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3678 8 9, g32p_row03_traceSegment_034_3678_0008, g32p_row03_traceSegment_034_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3703 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3695 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3695 8 9, g32p_row03_traceSegment_034_3695_0008, g32p_row03_traceSegment_034_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3678 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3678 17 17, g32p_row03_traceSegment_034_3678_0017, g32p_row03_traceSegment_034_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 3645 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3645 33 34, g32p_row03_traceSegment_034_3645_0033, g32p_row03_traceSegment_034_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3712 8 9, g32p_row03_traceSegment_034_3712_0008, g32p_row03_traceSegment_034_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3729 8 9, g32p_row03_traceSegment_034_3729_0008, g32p_row03_traceSegment_034_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3712 17 17, g32p_row03_traceSegment_034_3712_0017, g32p_row03_traceSegment_034_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3754 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3746 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3746 8 9, g32p_row03_traceSegment_034_3746_0008, g32p_row03_traceSegment_034_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3763 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3763 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3763 8 9, g32p_row03_traceSegment_034_3763_0008, g32p_row03_traceSegment_034_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3746 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3746 17 17, g32p_row03_traceSegment_034_3746_0017, g32p_row03_traceSegment_034_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 3712 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3712 34 34, g32p_row03_traceSegment_034_3712_0034, g32p_row03_traceSegment_034_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 3645 135 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3645 67 68, g32p_row03_traceSegment_034_3645_0067, g32p_row03_traceSegment_034_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 3510 270 = [0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3510 135 135, g32p_row03_traceSegment_034_3510_0135, g32p_row03_traceSegment_034_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_034 3240 540 = [0, 9, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3240 270 270, g32p_row03_traceSegment_034_3240_0270, g32p_row03_traceSegment_034_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 3780 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3796 8 9, g32p_row03_traceSegment_034_3796_0008, g32p_row03_traceSegment_034_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 3780 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3780 16 17, g32p_row03_traceSegment_034_3780_0016, g32p_row03_traceSegment_034_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3813 8 9, g32p_row03_traceSegment_034_3813_0008, g32p_row03_traceSegment_034_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3830 8 9, g32p_row03_traceSegment_034_3830_0008, g32p_row03_traceSegment_034_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3813 17 17, g32p_row03_traceSegment_034_3813_0017, g32p_row03_traceSegment_034_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 3780 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3780 33 34, g32p_row03_traceSegment_034_3780_0033, g32p_row03_traceSegment_034_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3847 8 9, g32p_row03_traceSegment_034_3847_0008, g32p_row03_traceSegment_034_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3864 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3864 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3864 8 9, g32p_row03_traceSegment_034_3864_0008, g32p_row03_traceSegment_034_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3847 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3847 17 17, g32p_row03_traceSegment_034_3847_0017, g32p_row03_traceSegment_034_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3889 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3881 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3881 8 9, g32p_row03_traceSegment_034_3881_0008, g32p_row03_traceSegment_034_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3898 8 9, g32p_row03_traceSegment_034_3898_0008, g32p_row03_traceSegment_034_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3881 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3881 17 17, g32p_row03_traceSegment_034_3881_0017, g32p_row03_traceSegment_034_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 3847 68 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3847 34 34, g32p_row03_traceSegment_034_3847_0034, g32p_row03_traceSegment_034_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 3780 135 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3780 67 68, g32p_row03_traceSegment_034_3780_0067, g32p_row03_traceSegment_034_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3931 8 9, g32p_row03_traceSegment_034_3931_0008, g32p_row03_traceSegment_034_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3915 16 17, g32p_row03_traceSegment_034_3915_0016, g32p_row03_traceSegment_034_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3948 8 9, g32p_row03_traceSegment_034_3948_0008, g32p_row03_traceSegment_034_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3965 8 9, g32p_row03_traceSegment_034_3965_0008, g32p_row03_traceSegment_034_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3948 17 17, g32p_row03_traceSegment_034_3948_0017, g32p_row03_traceSegment_034_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3915 33 34, g32p_row03_traceSegment_034_3915_0033, g32p_row03_traceSegment_034_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 3990 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3982 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3982 8 9, g32p_row03_traceSegment_034_3982_0008, g32p_row03_traceSegment_034_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3999 8 9, g32p_row03_traceSegment_034_3999_0008, g32p_row03_traceSegment_034_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 3982 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3982 17 17, g32p_row03_traceSegment_034_3982_0017, g32p_row03_traceSegment_034_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4016 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4016 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4016 8 9, g32p_row03_traceSegment_034_4016_0008, g32p_row03_traceSegment_034_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4041 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4033 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4033 8 9, g32p_row03_traceSegment_034_4033_0008, g32p_row03_traceSegment_034_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 4016 34 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4016 17 17, g32p_row03_traceSegment_034_4016_0017, g32p_row03_traceSegment_034_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 3982 68 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3982 34 34, g32p_row03_traceSegment_034_3982_0034, g32p_row03_traceSegment_034_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 3915 135 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3915 67 68, g32p_row03_traceSegment_034_3915_0067, g32p_row03_traceSegment_034_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 3780 270 = [0, 2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3780 135 135, g32p_row03_traceSegment_034_3780_0135, g32p_row03_traceSegment_034_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4066 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4074 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4066 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4066 8 9, g32p_row03_traceSegment_034_4066_0008, g32p_row03_traceSegment_034_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 4050 33 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4050 16 17, g32p_row03_traceSegment_034_4050_0016, g32p_row03_traceSegment_034_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4083 8 9, g32p_row03_traceSegment_034_4083_0008, g32p_row03_traceSegment_034_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4108 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4100 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4100 8 9, g32p_row03_traceSegment_034_4100_0008, g32p_row03_traceSegment_034_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 4083 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4083 17 17, g32p_row03_traceSegment_034_4083_0017, g32p_row03_traceSegment_034_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 4050 67 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4050 33 34, g32p_row03_traceSegment_034_4050_0033, g32p_row03_traceSegment_034_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4117 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4117 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4117 8 9, g32p_row03_traceSegment_034_4117_0008, g32p_row03_traceSegment_034_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4134 8 9, g32p_row03_traceSegment_034_4134_0008, g32p_row03_traceSegment_034_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 4117 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4117 17 17, g32p_row03_traceSegment_034_4117_0017, g32p_row03_traceSegment_034_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4151 8 9, g32p_row03_traceSegment_034_4151_0008, g32p_row03_traceSegment_034_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4168 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4168 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4168 8 9, g32p_row03_traceSegment_034_4168_0008, g32p_row03_traceSegment_034_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 4151 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4151 17 17, g32p_row03_traceSegment_034_4151_0017, g32p_row03_traceSegment_034_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 4117 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4117 34 34, g32p_row03_traceSegment_034_4117_0034, g32p_row03_traceSegment_034_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 4050 135 = [0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4050 67 68, g32p_row03_traceSegment_034_4050_0067, g32p_row03_traceSegment_034_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_034 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4201 8 9, g32p_row03_traceSegment_034_4201_0008, g32p_row03_traceSegment_034_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_034 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4185 16 17, g32p_row03_traceSegment_034_4185_0016, g32p_row03_traceSegment_034_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4218 8 9, g32p_row03_traceSegment_034_4218_0008, g32p_row03_traceSegment_034_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4235 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4243 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4235 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4235 8 9, g32p_row03_traceSegment_034_4235_0008, g32p_row03_traceSegment_034_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 4218 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4218 17 17, g32p_row03_traceSegment_034_4218_0017, g32p_row03_traceSegment_034_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_034 4185 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4185 33 34, g32p_row03_traceSegment_034_4185_0033, g32p_row03_traceSegment_034_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4252 8 9, g32p_row03_traceSegment_034_4252_0008, g32p_row03_traceSegment_034_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4269 8 9, g32p_row03_traceSegment_034_4269_0008, g32p_row03_traceSegment_034_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4252 17 17, g32p_row03_traceSegment_034_4252_0017, g32p_row03_traceSegment_034_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4286 8 9, g32p_row03_traceSegment_034_4286_0008, g32p_row03_traceSegment_034_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_034 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_034 4311 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_034_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_034 4303 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4303 8 9, g32p_row03_traceSegment_034_4303_0008, g32p_row03_traceSegment_034_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_034 4286 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4286 17 17, g32p_row03_traceSegment_034_4286_0017, g32p_row03_traceSegment_034_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_034 4252 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4252 34 34, g32p_row03_traceSegment_034_4252_0034, g32p_row03_traceSegment_034_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_034 4185 135 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4185 67 68, g32p_row03_traceSegment_034_4185_0067, g32p_row03_traceSegment_034_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_034_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_034 4050 270 = [0, 3, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 4050 135 135, g32p_row03_traceSegment_034_4050_0135, g32p_row03_traceSegment_034_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_034 3780 540 = [0, 5, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3780 270 270, g32p_row03_traceSegment_034_3780_0270, g32p_row03_traceSegment_034_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_034_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_034 3240 1080 = [0, 14, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 3240 540 540, g32p_row03_traceSegment_034_3240_0540, g32p_row03_traceSegment_034_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_034_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_034 2160 2160 = [0, 29, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 2160 1080 1080, g32p_row03_traceSegment_034_2160_1080, g32p_row03_traceSegment_034_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_034_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_034 0 4320 = [0, 30, 0, 0, 90] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_034 0 2160 2160, g32p_row03_traceSegment_034_0000_2160, g32p_row03_traceSegment_034_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 34 = [0, 30, 0, 0, 90] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_034_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 18) (g32p_literalTraceValue 2 18)
      [1, -1, 1] [51840, 51840] = true := by
  rw [g32p_row03_traceCoefficients_018]
  decide +kernel

theorem g32p_row03_tracePolynomial_021 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 21) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 21) (g32p_literalTraceValue 2 21)
      [1, -1, 1] [8640, 8640] = true := by
  rw [g32p_row03_traceCoefficients_021]
  decide +kernel

theorem g32p_row03_tracePolynomial_022 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 22) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 22) (g32p_literalTraceValue 2 22)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_022]
  decide +kernel

theorem g32p_row03_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 24) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 24) (g32p_literalTraceValue 2 24)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_024]
  decide +kernel

theorem g32p_row03_tracePolynomial_026 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 26) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 26) (g32p_literalTraceValue 2 26)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_026]
  decide +kernel

theorem g32p_row03_tracePolynomial_030 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 30) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 30) (g32p_literalTraceValue 2 30)
      [1, -1, 1] [-8640] = true := by
  rw [g32p_row03_traceCoefficients_030]
  decide +kernel

theorem g32p_row03_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 32) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 32) (g32p_literalTraceValue 2 32)
      [1, -1, 1] [12960, 12960, 12960] = true := by
  rw [g32p_row03_traceCoefficients_032]
  decide +kernel

theorem g32p_row03_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 34) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 34) (g32p_literalTraceValue 2 34)
      [1, -1, 1] [17280, 25920, 25920] = true := by
  rw [g32p_row03_traceCoefficients_034]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
