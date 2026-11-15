import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0332
import HodgeLean.Foundations.Program.G32PropFourSixPacked0331
import HodgeLean.Foundations.Program.G32PropFourSixPacked0330

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_096_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 16 8 9, g32p_row03_traceSegment_096_0016_0008, g32p_row03_traceSegment_096_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 0 16 17, g32p_row03_traceSegment_096_0000_0016, g32p_row03_traceSegment_096_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 33 8 9, g32p_row03_traceSegment_096_0033_0008, g32p_row03_traceSegment_096_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 50 8 9, g32p_row03_traceSegment_096_0050_0008, g32p_row03_traceSegment_096_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 33 17 17, g32p_row03_traceSegment_096_0033_0017, g32p_row03_traceSegment_096_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 0 33 34, g32p_row03_traceSegment_096_0000_0033, g32p_row03_traceSegment_096_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 67 8 9, g32p_row03_traceSegment_096_0067_0008, g32p_row03_traceSegment_096_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 84 8 9, g32p_row03_traceSegment_096_0084_0008, g32p_row03_traceSegment_096_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 67 17 17, g32p_row03_traceSegment_096_0067_0017, g32p_row03_traceSegment_096_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 101 8 9, g32p_row03_traceSegment_096_0101_0008, g32p_row03_traceSegment_096_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 118 8 9, g32p_row03_traceSegment_096_0118_0008, g32p_row03_traceSegment_096_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 101 17 17, g32p_row03_traceSegment_096_0101_0017, g32p_row03_traceSegment_096_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 67 34 34, g32p_row03_traceSegment_096_0067_0034, g32p_row03_traceSegment_096_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 0 67 68, g32p_row03_traceSegment_096_0000_0067, g32p_row03_traceSegment_096_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 151 8 9, g32p_row03_traceSegment_096_0151_0008, g32p_row03_traceSegment_096_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 135 16 17, g32p_row03_traceSegment_096_0135_0016, g32p_row03_traceSegment_096_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 168 8 9, g32p_row03_traceSegment_096_0168_0008, g32p_row03_traceSegment_096_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 185 8 9, g32p_row03_traceSegment_096_0185_0008, g32p_row03_traceSegment_096_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 168 17 17, g32p_row03_traceSegment_096_0168_0017, g32p_row03_traceSegment_096_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 135 33 34, g32p_row03_traceSegment_096_0135_0033, g32p_row03_traceSegment_096_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 202 8 9, g32p_row03_traceSegment_096_0202_0008, g32p_row03_traceSegment_096_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 227 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 219 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 219 8 9, g32p_row03_traceSegment_096_0219_0008, g32p_row03_traceSegment_096_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 202 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 202 17 17, g32p_row03_traceSegment_096_0202_0017, g32p_row03_traceSegment_096_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 236 8 9, g32p_row03_traceSegment_096_0236_0008, g32p_row03_traceSegment_096_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 253 8 9, g32p_row03_traceSegment_096_0253_0008, g32p_row03_traceSegment_096_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 236 17 17, g32p_row03_traceSegment_096_0236_0017, g32p_row03_traceSegment_096_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 202 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 202 34 34, g32p_row03_traceSegment_096_0202_0034, g32p_row03_traceSegment_096_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 135 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 135 67 68, g32p_row03_traceSegment_096_0135_0067, g32p_row03_traceSegment_096_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 0 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 0 135 135, g32p_row03_traceSegment_096_0000_0135, g32p_row03_traceSegment_096_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 286 8 9, g32p_row03_traceSegment_096_0286_0008, g32p_row03_traceSegment_096_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 270 16 17, g32p_row03_traceSegment_096_0270_0016, g32p_row03_traceSegment_096_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 303 8 9, g32p_row03_traceSegment_096_0303_0008, g32p_row03_traceSegment_096_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 320 8 9, g32p_row03_traceSegment_096_0320_0008, g32p_row03_traceSegment_096_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 303 17 17, g32p_row03_traceSegment_096_0303_0017, g32p_row03_traceSegment_096_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 270 33 34, g32p_row03_traceSegment_096_0270_0033, g32p_row03_traceSegment_096_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 337 8 9, g32p_row03_traceSegment_096_0337_0008, g32p_row03_traceSegment_096_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 354 8 9, g32p_row03_traceSegment_096_0354_0008, g32p_row03_traceSegment_096_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 337 17 17, g32p_row03_traceSegment_096_0337_0017, g32p_row03_traceSegment_096_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 371 8 9, g32p_row03_traceSegment_096_0371_0008, g32p_row03_traceSegment_096_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 388 8 9, g32p_row03_traceSegment_096_0388_0008, g32p_row03_traceSegment_096_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 371 17 17, g32p_row03_traceSegment_096_0371_0017, g32p_row03_traceSegment_096_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 337 34 34, g32p_row03_traceSegment_096_0337_0034, g32p_row03_traceSegment_096_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 270 67 68, g32p_row03_traceSegment_096_0270_0067, g32p_row03_traceSegment_096_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 421 8 9, g32p_row03_traceSegment_096_0421_0008, g32p_row03_traceSegment_096_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 405 16 17, g32p_row03_traceSegment_096_0405_0016, g32p_row03_traceSegment_096_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 438 8 9, g32p_row03_traceSegment_096_0438_0008, g32p_row03_traceSegment_096_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 455 8 9, g32p_row03_traceSegment_096_0455_0008, g32p_row03_traceSegment_096_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 438 17 17, g32p_row03_traceSegment_096_0438_0017, g32p_row03_traceSegment_096_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 405 33 34, g32p_row03_traceSegment_096_0405_0033, g32p_row03_traceSegment_096_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 472 8 9, g32p_row03_traceSegment_096_0472_0008, g32p_row03_traceSegment_096_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 489 8 9, g32p_row03_traceSegment_096_0489_0008, g32p_row03_traceSegment_096_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 472 17 17, g32p_row03_traceSegment_096_0472_0017, g32p_row03_traceSegment_096_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 506 8 9, g32p_row03_traceSegment_096_0506_0008, g32p_row03_traceSegment_096_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 523 8 9, g32p_row03_traceSegment_096_0523_0008, g32p_row03_traceSegment_096_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 506 17 17, g32p_row03_traceSegment_096_0506_0017, g32p_row03_traceSegment_096_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 472 34 34, g32p_row03_traceSegment_096_0472_0034, g32p_row03_traceSegment_096_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 405 67 68, g32p_row03_traceSegment_096_0405_0067, g32p_row03_traceSegment_096_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 270 135 135, g32p_row03_traceSegment_096_0270_0135, g32p_row03_traceSegment_096_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_096 0 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 0 270 270, g32p_row03_traceSegment_096_0000_0270, g32p_row03_traceSegment_096_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 556 8 9, g32p_row03_traceSegment_096_0556_0008, g32p_row03_traceSegment_096_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 540 16 17, g32p_row03_traceSegment_096_0540_0016, g32p_row03_traceSegment_096_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 573 8 9, g32p_row03_traceSegment_096_0573_0008, g32p_row03_traceSegment_096_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 590 8 9, g32p_row03_traceSegment_096_0590_0008, g32p_row03_traceSegment_096_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 573 17 17, g32p_row03_traceSegment_096_0573_0017, g32p_row03_traceSegment_096_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 540 33 34, g32p_row03_traceSegment_096_0540_0033, g32p_row03_traceSegment_096_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 607 8 9, g32p_row03_traceSegment_096_0607_0008, g32p_row03_traceSegment_096_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 624 8 9, g32p_row03_traceSegment_096_0624_0008, g32p_row03_traceSegment_096_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 607 17 17, g32p_row03_traceSegment_096_0607_0017, g32p_row03_traceSegment_096_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 641 8 9, g32p_row03_traceSegment_096_0641_0008, g32p_row03_traceSegment_096_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 658 8 9, g32p_row03_traceSegment_096_0658_0008, g32p_row03_traceSegment_096_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 641 17 17, g32p_row03_traceSegment_096_0641_0017, g32p_row03_traceSegment_096_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 607 34 34, g32p_row03_traceSegment_096_0607_0034, g32p_row03_traceSegment_096_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 540 67 68, g32p_row03_traceSegment_096_0540_0067, g32p_row03_traceSegment_096_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 691 8 9, g32p_row03_traceSegment_096_0691_0008, g32p_row03_traceSegment_096_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 675 16 17, g32p_row03_traceSegment_096_0675_0016, g32p_row03_traceSegment_096_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 708 8 9, g32p_row03_traceSegment_096_0708_0008, g32p_row03_traceSegment_096_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 725 8 9, g32p_row03_traceSegment_096_0725_0008, g32p_row03_traceSegment_096_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 708 17 17, g32p_row03_traceSegment_096_0708_0017, g32p_row03_traceSegment_096_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 675 33 34, g32p_row03_traceSegment_096_0675_0033, g32p_row03_traceSegment_096_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 742 8 9, g32p_row03_traceSegment_096_0742_0008, g32p_row03_traceSegment_096_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 759 8 9, g32p_row03_traceSegment_096_0759_0008, g32p_row03_traceSegment_096_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 742 17 17, g32p_row03_traceSegment_096_0742_0017, g32p_row03_traceSegment_096_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 776 8 9, g32p_row03_traceSegment_096_0776_0008, g32p_row03_traceSegment_096_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 793 8 9, g32p_row03_traceSegment_096_0793_0008, g32p_row03_traceSegment_096_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 776 17 17, g32p_row03_traceSegment_096_0776_0017, g32p_row03_traceSegment_096_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 742 34 34, g32p_row03_traceSegment_096_0742_0034, g32p_row03_traceSegment_096_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 675 67 68, g32p_row03_traceSegment_096_0675_0067, g32p_row03_traceSegment_096_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 540 135 135, g32p_row03_traceSegment_096_0540_0135, g32p_row03_traceSegment_096_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 826 8 9, g32p_row03_traceSegment_096_0826_0008, g32p_row03_traceSegment_096_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 810 16 17, g32p_row03_traceSegment_096_0810_0016, g32p_row03_traceSegment_096_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 843 8 9, g32p_row03_traceSegment_096_0843_0008, g32p_row03_traceSegment_096_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 860 8 9, g32p_row03_traceSegment_096_0860_0008, g32p_row03_traceSegment_096_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 843 17 17, g32p_row03_traceSegment_096_0843_0017, g32p_row03_traceSegment_096_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 810 33 34, g32p_row03_traceSegment_096_0810_0033, g32p_row03_traceSegment_096_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 877 8 9, g32p_row03_traceSegment_096_0877_0008, g32p_row03_traceSegment_096_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 894 8 9, g32p_row03_traceSegment_096_0894_0008, g32p_row03_traceSegment_096_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 877 17 17, g32p_row03_traceSegment_096_0877_0017, g32p_row03_traceSegment_096_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 911 8 9, g32p_row03_traceSegment_096_0911_0008, g32p_row03_traceSegment_096_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 928 8 9, g32p_row03_traceSegment_096_0928_0008, g32p_row03_traceSegment_096_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 911 17 17, g32p_row03_traceSegment_096_0911_0017, g32p_row03_traceSegment_096_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 877 34 34, g32p_row03_traceSegment_096_0877_0034, g32p_row03_traceSegment_096_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 810 67 68, g32p_row03_traceSegment_096_0810_0067, g32p_row03_traceSegment_096_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 961 8 9, g32p_row03_traceSegment_096_0961_0008, g32p_row03_traceSegment_096_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 945 16 17, g32p_row03_traceSegment_096_0945_0016, g32p_row03_traceSegment_096_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 978 8 9, g32p_row03_traceSegment_096_0978_0008, g32p_row03_traceSegment_096_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 995 8 9, g32p_row03_traceSegment_096_0995_0008, g32p_row03_traceSegment_096_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 978 17 17, g32p_row03_traceSegment_096_0978_0017, g32p_row03_traceSegment_096_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 945 33 34, g32p_row03_traceSegment_096_0945_0033, g32p_row03_traceSegment_096_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1012 8 9, g32p_row03_traceSegment_096_1012_0008, g32p_row03_traceSegment_096_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1029 8 9, g32p_row03_traceSegment_096_1029_0008, g32p_row03_traceSegment_096_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1012 17 17, g32p_row03_traceSegment_096_1012_0017, g32p_row03_traceSegment_096_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1046 8 9, g32p_row03_traceSegment_096_1046_0008, g32p_row03_traceSegment_096_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1063 8 9, g32p_row03_traceSegment_096_1063_0008, g32p_row03_traceSegment_096_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1046 17 17, g32p_row03_traceSegment_096_1046_0017, g32p_row03_traceSegment_096_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1012 34 34, g32p_row03_traceSegment_096_1012_0034, g32p_row03_traceSegment_096_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 945 67 68, g32p_row03_traceSegment_096_0945_0067, g32p_row03_traceSegment_096_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 810 135 135, g32p_row03_traceSegment_096_0810_0135, g32p_row03_traceSegment_096_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_096 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 540 270 270, g32p_row03_traceSegment_096_0540_0270, g32p_row03_traceSegment_096_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_096 0 1080 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 0 540 540, g32p_row03_traceSegment_096_0000_0540, g32p_row03_traceSegment_096_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1096 8 9, g32p_row03_traceSegment_096_1096_0008, g32p_row03_traceSegment_096_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1080 16 17, g32p_row03_traceSegment_096_1080_0016, g32p_row03_traceSegment_096_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1113 8 9, g32p_row03_traceSegment_096_1113_0008, g32p_row03_traceSegment_096_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1130 8 9, g32p_row03_traceSegment_096_1130_0008, g32p_row03_traceSegment_096_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1113 17 17, g32p_row03_traceSegment_096_1113_0017, g32p_row03_traceSegment_096_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1080 33 34, g32p_row03_traceSegment_096_1080_0033, g32p_row03_traceSegment_096_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1147 8 9, g32p_row03_traceSegment_096_1147_0008, g32p_row03_traceSegment_096_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1164 8 9, g32p_row03_traceSegment_096_1164_0008, g32p_row03_traceSegment_096_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1147 17 17, g32p_row03_traceSegment_096_1147_0017, g32p_row03_traceSegment_096_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1181 8 9, g32p_row03_traceSegment_096_1181_0008, g32p_row03_traceSegment_096_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1198 8 9, g32p_row03_traceSegment_096_1198_0008, g32p_row03_traceSegment_096_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1181 17 17, g32p_row03_traceSegment_096_1181_0017, g32p_row03_traceSegment_096_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1147 34 34, g32p_row03_traceSegment_096_1147_0034, g32p_row03_traceSegment_096_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1080 67 68, g32p_row03_traceSegment_096_1080_0067, g32p_row03_traceSegment_096_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1231 8 9, g32p_row03_traceSegment_096_1231_0008, g32p_row03_traceSegment_096_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1215 16 17, g32p_row03_traceSegment_096_1215_0016, g32p_row03_traceSegment_096_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1248 8 9, g32p_row03_traceSegment_096_1248_0008, g32p_row03_traceSegment_096_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1265 8 9, g32p_row03_traceSegment_096_1265_0008, g32p_row03_traceSegment_096_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1248 17 17, g32p_row03_traceSegment_096_1248_0017, g32p_row03_traceSegment_096_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1215 33 34, g32p_row03_traceSegment_096_1215_0033, g32p_row03_traceSegment_096_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1282 8 9, g32p_row03_traceSegment_096_1282_0008, g32p_row03_traceSegment_096_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1299 8 9, g32p_row03_traceSegment_096_1299_0008, g32p_row03_traceSegment_096_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1282 17 17, g32p_row03_traceSegment_096_1282_0017, g32p_row03_traceSegment_096_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1316 8 9, g32p_row03_traceSegment_096_1316_0008, g32p_row03_traceSegment_096_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1333 8 9, g32p_row03_traceSegment_096_1333_0008, g32p_row03_traceSegment_096_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1316 17 17, g32p_row03_traceSegment_096_1316_0017, g32p_row03_traceSegment_096_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1282 34 34, g32p_row03_traceSegment_096_1282_0034, g32p_row03_traceSegment_096_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1215 67 68, g32p_row03_traceSegment_096_1215_0067, g32p_row03_traceSegment_096_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1080 135 135, g32p_row03_traceSegment_096_1080_0135, g32p_row03_traceSegment_096_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1366 8 9, g32p_row03_traceSegment_096_1366_0008, g32p_row03_traceSegment_096_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1350 16 17, g32p_row03_traceSegment_096_1350_0016, g32p_row03_traceSegment_096_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1383 8 9, g32p_row03_traceSegment_096_1383_0008, g32p_row03_traceSegment_096_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1400 8 9, g32p_row03_traceSegment_096_1400_0008, g32p_row03_traceSegment_096_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1383 17 17, g32p_row03_traceSegment_096_1383_0017, g32p_row03_traceSegment_096_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1350 33 34, g32p_row03_traceSegment_096_1350_0033, g32p_row03_traceSegment_096_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1417 8 9, g32p_row03_traceSegment_096_1417_0008, g32p_row03_traceSegment_096_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1434 8 9, g32p_row03_traceSegment_096_1434_0008, g32p_row03_traceSegment_096_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1417 17 17, g32p_row03_traceSegment_096_1417_0017, g32p_row03_traceSegment_096_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1451 8 9, g32p_row03_traceSegment_096_1451_0008, g32p_row03_traceSegment_096_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1468 8 9, g32p_row03_traceSegment_096_1468_0008, g32p_row03_traceSegment_096_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1451 17 17, g32p_row03_traceSegment_096_1451_0017, g32p_row03_traceSegment_096_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1417 34 34, g32p_row03_traceSegment_096_1417_0034, g32p_row03_traceSegment_096_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1350 67 68, g32p_row03_traceSegment_096_1350_0067, g32p_row03_traceSegment_096_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1501 8 9, g32p_row03_traceSegment_096_1501_0008, g32p_row03_traceSegment_096_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1485 16 17, g32p_row03_traceSegment_096_1485_0016, g32p_row03_traceSegment_096_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1518 8 9, g32p_row03_traceSegment_096_1518_0008, g32p_row03_traceSegment_096_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1535 8 9, g32p_row03_traceSegment_096_1535_0008, g32p_row03_traceSegment_096_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1518 17 17, g32p_row03_traceSegment_096_1518_0017, g32p_row03_traceSegment_096_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1485 33 34, g32p_row03_traceSegment_096_1485_0033, g32p_row03_traceSegment_096_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1552 8 9, g32p_row03_traceSegment_096_1552_0008, g32p_row03_traceSegment_096_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1569 8 9, g32p_row03_traceSegment_096_1569_0008, g32p_row03_traceSegment_096_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1552 17 17, g32p_row03_traceSegment_096_1552_0017, g32p_row03_traceSegment_096_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1586 8 9, g32p_row03_traceSegment_096_1586_0008, g32p_row03_traceSegment_096_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1603 8 9, g32p_row03_traceSegment_096_1603_0008, g32p_row03_traceSegment_096_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1586 17 17, g32p_row03_traceSegment_096_1586_0017, g32p_row03_traceSegment_096_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1552 34 34, g32p_row03_traceSegment_096_1552_0034, g32p_row03_traceSegment_096_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1485 67 68, g32p_row03_traceSegment_096_1485_0067, g32p_row03_traceSegment_096_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1350 135 135, g32p_row03_traceSegment_096_1350_0135, g32p_row03_traceSegment_096_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_096 1080 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1080 270 270, g32p_row03_traceSegment_096_1080_0270, g32p_row03_traceSegment_096_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1636 8 9, g32p_row03_traceSegment_096_1636_0008, g32p_row03_traceSegment_096_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1620 16 17, g32p_row03_traceSegment_096_1620_0016, g32p_row03_traceSegment_096_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1653 8 9, g32p_row03_traceSegment_096_1653_0008, g32p_row03_traceSegment_096_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1670 8 9, g32p_row03_traceSegment_096_1670_0008, g32p_row03_traceSegment_096_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1653 17 17, g32p_row03_traceSegment_096_1653_0017, g32p_row03_traceSegment_096_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1620 33 34, g32p_row03_traceSegment_096_1620_0033, g32p_row03_traceSegment_096_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1687 8 9, g32p_row03_traceSegment_096_1687_0008, g32p_row03_traceSegment_096_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1704 8 9, g32p_row03_traceSegment_096_1704_0008, g32p_row03_traceSegment_096_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1687 17 17, g32p_row03_traceSegment_096_1687_0017, g32p_row03_traceSegment_096_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1721 8 9, g32p_row03_traceSegment_096_1721_0008, g32p_row03_traceSegment_096_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1738 8 9, g32p_row03_traceSegment_096_1738_0008, g32p_row03_traceSegment_096_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1721 17 17, g32p_row03_traceSegment_096_1721_0017, g32p_row03_traceSegment_096_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1687 34 34, g32p_row03_traceSegment_096_1687_0034, g32p_row03_traceSegment_096_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1620 67 68, g32p_row03_traceSegment_096_1620_0067, g32p_row03_traceSegment_096_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1771 8 9, g32p_row03_traceSegment_096_1771_0008, g32p_row03_traceSegment_096_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1755 16 17, g32p_row03_traceSegment_096_1755_0016, g32p_row03_traceSegment_096_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1788 8 9, g32p_row03_traceSegment_096_1788_0008, g32p_row03_traceSegment_096_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1805 8 9, g32p_row03_traceSegment_096_1805_0008, g32p_row03_traceSegment_096_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1788 17 17, g32p_row03_traceSegment_096_1788_0017, g32p_row03_traceSegment_096_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1755 33 34, g32p_row03_traceSegment_096_1755_0033, g32p_row03_traceSegment_096_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1822 8 9, g32p_row03_traceSegment_096_1822_0008, g32p_row03_traceSegment_096_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1839 8 9, g32p_row03_traceSegment_096_1839_0008, g32p_row03_traceSegment_096_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1822 17 17, g32p_row03_traceSegment_096_1822_0017, g32p_row03_traceSegment_096_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1856 8 9, g32p_row03_traceSegment_096_1856_0008, g32p_row03_traceSegment_096_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1873 8 9, g32p_row03_traceSegment_096_1873_0008, g32p_row03_traceSegment_096_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1856 17 17, g32p_row03_traceSegment_096_1856_0017, g32p_row03_traceSegment_096_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1822 34 34, g32p_row03_traceSegment_096_1822_0034, g32p_row03_traceSegment_096_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1755 67 68, g32p_row03_traceSegment_096_1755_0067, g32p_row03_traceSegment_096_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1620 135 135, g32p_row03_traceSegment_096_1620_0135, g32p_row03_traceSegment_096_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1906 8 9, g32p_row03_traceSegment_096_1906_0008, g32p_row03_traceSegment_096_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1890 16 17, g32p_row03_traceSegment_096_1890_0016, g32p_row03_traceSegment_096_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1923 8 9, g32p_row03_traceSegment_096_1923_0008, g32p_row03_traceSegment_096_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1940 8 9, g32p_row03_traceSegment_096_1940_0008, g32p_row03_traceSegment_096_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1923 17 17, g32p_row03_traceSegment_096_1923_0017, g32p_row03_traceSegment_096_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1890 33 34, g32p_row03_traceSegment_096_1890_0033, g32p_row03_traceSegment_096_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1957 8 9, g32p_row03_traceSegment_096_1957_0008, g32p_row03_traceSegment_096_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1974 8 9, g32p_row03_traceSegment_096_1974_0008, g32p_row03_traceSegment_096_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1957 17 17, g32p_row03_traceSegment_096_1957_0017, g32p_row03_traceSegment_096_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1991 8 9, g32p_row03_traceSegment_096_1991_0008, g32p_row03_traceSegment_096_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2008 8 9, g32p_row03_traceSegment_096_2008_0008, g32p_row03_traceSegment_096_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1991 17 17, g32p_row03_traceSegment_096_1991_0017, g32p_row03_traceSegment_096_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1957 34 34, g32p_row03_traceSegment_096_1957_0034, g32p_row03_traceSegment_096_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1890 67 68, g32p_row03_traceSegment_096_1890_0067, g32p_row03_traceSegment_096_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2041 8 9, g32p_row03_traceSegment_096_2041_0008, g32p_row03_traceSegment_096_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2025 16 17, g32p_row03_traceSegment_096_2025_0016, g32p_row03_traceSegment_096_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2058 8 9, g32p_row03_traceSegment_096_2058_0008, g32p_row03_traceSegment_096_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2075 8 9, g32p_row03_traceSegment_096_2075_0008, g32p_row03_traceSegment_096_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2058 17 17, g32p_row03_traceSegment_096_2058_0017, g32p_row03_traceSegment_096_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2025 33 34, g32p_row03_traceSegment_096_2025_0033, g32p_row03_traceSegment_096_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2092 8 9, g32p_row03_traceSegment_096_2092_0008, g32p_row03_traceSegment_096_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2109 8 9, g32p_row03_traceSegment_096_2109_0008, g32p_row03_traceSegment_096_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2092 17 17, g32p_row03_traceSegment_096_2092_0017, g32p_row03_traceSegment_096_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2126 8 9, g32p_row03_traceSegment_096_2126_0008, g32p_row03_traceSegment_096_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2143 8 9, g32p_row03_traceSegment_096_2143_0008, g32p_row03_traceSegment_096_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2126 17 17, g32p_row03_traceSegment_096_2126_0017, g32p_row03_traceSegment_096_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2092 34 34, g32p_row03_traceSegment_096_2092_0034, g32p_row03_traceSegment_096_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2025 67 68, g32p_row03_traceSegment_096_2025_0067, g32p_row03_traceSegment_096_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 1890 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1890 135 135, g32p_row03_traceSegment_096_1890_0135, g32p_row03_traceSegment_096_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_096 1620 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1620 270 270, g32p_row03_traceSegment_096_1620_0270, g32p_row03_traceSegment_096_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_096_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_096 1080 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 1080 540 540, g32p_row03_traceSegment_096_1080_0540, g32p_row03_traceSegment_096_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_096 0 2160 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 0 1080 1080, g32p_row03_traceSegment_096_0000_1080, g32p_row03_traceSegment_096_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2176 8 9, g32p_row03_traceSegment_096_2176_0008, g32p_row03_traceSegment_096_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2160 16 17, g32p_row03_traceSegment_096_2160_0016, g32p_row03_traceSegment_096_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2193 8 9, g32p_row03_traceSegment_096_2193_0008, g32p_row03_traceSegment_096_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2210 8 9, g32p_row03_traceSegment_096_2210_0008, g32p_row03_traceSegment_096_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2193 17 17, g32p_row03_traceSegment_096_2193_0017, g32p_row03_traceSegment_096_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2160 33 34, g32p_row03_traceSegment_096_2160_0033, g32p_row03_traceSegment_096_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2227 8 9, g32p_row03_traceSegment_096_2227_0008, g32p_row03_traceSegment_096_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2244 8 9, g32p_row03_traceSegment_096_2244_0008, g32p_row03_traceSegment_096_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2227 17 17, g32p_row03_traceSegment_096_2227_0017, g32p_row03_traceSegment_096_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2261 8 9, g32p_row03_traceSegment_096_2261_0008, g32p_row03_traceSegment_096_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2278 8 9, g32p_row03_traceSegment_096_2278_0008, g32p_row03_traceSegment_096_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2261 17 17, g32p_row03_traceSegment_096_2261_0017, g32p_row03_traceSegment_096_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2227 34 34, g32p_row03_traceSegment_096_2227_0034, g32p_row03_traceSegment_096_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2160 67 68, g32p_row03_traceSegment_096_2160_0067, g32p_row03_traceSegment_096_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2311 8 9, g32p_row03_traceSegment_096_2311_0008, g32p_row03_traceSegment_096_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2295 16 17, g32p_row03_traceSegment_096_2295_0016, g32p_row03_traceSegment_096_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2328 8 9, g32p_row03_traceSegment_096_2328_0008, g32p_row03_traceSegment_096_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2345 8 9, g32p_row03_traceSegment_096_2345_0008, g32p_row03_traceSegment_096_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2328 17 17, g32p_row03_traceSegment_096_2328_0017, g32p_row03_traceSegment_096_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2295 33 34, g32p_row03_traceSegment_096_2295_0033, g32p_row03_traceSegment_096_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2362 8 9, g32p_row03_traceSegment_096_2362_0008, g32p_row03_traceSegment_096_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2379 8 9, g32p_row03_traceSegment_096_2379_0008, g32p_row03_traceSegment_096_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2362 17 17, g32p_row03_traceSegment_096_2362_0017, g32p_row03_traceSegment_096_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2396 8 9, g32p_row03_traceSegment_096_2396_0008, g32p_row03_traceSegment_096_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2413 8 9, g32p_row03_traceSegment_096_2413_0008, g32p_row03_traceSegment_096_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2396 17 17, g32p_row03_traceSegment_096_2396_0017, g32p_row03_traceSegment_096_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2362 34 34, g32p_row03_traceSegment_096_2362_0034, g32p_row03_traceSegment_096_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2295 67 68, g32p_row03_traceSegment_096_2295_0067, g32p_row03_traceSegment_096_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 2160 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2160 135 135, g32p_row03_traceSegment_096_2160_0135, g32p_row03_traceSegment_096_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2446 8 9, g32p_row03_traceSegment_096_2446_0008, g32p_row03_traceSegment_096_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2430 16 17, g32p_row03_traceSegment_096_2430_0016, g32p_row03_traceSegment_096_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2463 8 9, g32p_row03_traceSegment_096_2463_0008, g32p_row03_traceSegment_096_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2480 8 9, g32p_row03_traceSegment_096_2480_0008, g32p_row03_traceSegment_096_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2463 17 17, g32p_row03_traceSegment_096_2463_0017, g32p_row03_traceSegment_096_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2430 33 34, g32p_row03_traceSegment_096_2430_0033, g32p_row03_traceSegment_096_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2497 8 9, g32p_row03_traceSegment_096_2497_0008, g32p_row03_traceSegment_096_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2514 8 9, g32p_row03_traceSegment_096_2514_0008, g32p_row03_traceSegment_096_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2497 17 17, g32p_row03_traceSegment_096_2497_0017, g32p_row03_traceSegment_096_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2531 8 9, g32p_row03_traceSegment_096_2531_0008, g32p_row03_traceSegment_096_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2548 8 9, g32p_row03_traceSegment_096_2548_0008, g32p_row03_traceSegment_096_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2531 17 17, g32p_row03_traceSegment_096_2531_0017, g32p_row03_traceSegment_096_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2497 34 34, g32p_row03_traceSegment_096_2497_0034, g32p_row03_traceSegment_096_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2430 67 68, g32p_row03_traceSegment_096_2430_0067, g32p_row03_traceSegment_096_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2581 8 9, g32p_row03_traceSegment_096_2581_0008, g32p_row03_traceSegment_096_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2565 16 17, g32p_row03_traceSegment_096_2565_0016, g32p_row03_traceSegment_096_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2598 8 9, g32p_row03_traceSegment_096_2598_0008, g32p_row03_traceSegment_096_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2615 8 9, g32p_row03_traceSegment_096_2615_0008, g32p_row03_traceSegment_096_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2598 17 17, g32p_row03_traceSegment_096_2598_0017, g32p_row03_traceSegment_096_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2565 33 34, g32p_row03_traceSegment_096_2565_0033, g32p_row03_traceSegment_096_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2632 8 9, g32p_row03_traceSegment_096_2632_0008, g32p_row03_traceSegment_096_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2649 8 9, g32p_row03_traceSegment_096_2649_0008, g32p_row03_traceSegment_096_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2632 17 17, g32p_row03_traceSegment_096_2632_0017, g32p_row03_traceSegment_096_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2666 8 9, g32p_row03_traceSegment_096_2666_0008, g32p_row03_traceSegment_096_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2683 8 9, g32p_row03_traceSegment_096_2683_0008, g32p_row03_traceSegment_096_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2666 17 17, g32p_row03_traceSegment_096_2666_0017, g32p_row03_traceSegment_096_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2632 34 34, g32p_row03_traceSegment_096_2632_0034, g32p_row03_traceSegment_096_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2565 67 68, g32p_row03_traceSegment_096_2565_0067, g32p_row03_traceSegment_096_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2430 135 135, g32p_row03_traceSegment_096_2430_0135, g32p_row03_traceSegment_096_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_096 2160 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2160 270 270, g32p_row03_traceSegment_096_2160_0270, g32p_row03_traceSegment_096_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2716 8 9, g32p_row03_traceSegment_096_2716_0008, g32p_row03_traceSegment_096_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2700 16 17, g32p_row03_traceSegment_096_2700_0016, g32p_row03_traceSegment_096_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2733 8 9, g32p_row03_traceSegment_096_2733_0008, g32p_row03_traceSegment_096_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2750 8 9, g32p_row03_traceSegment_096_2750_0008, g32p_row03_traceSegment_096_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2733 17 17, g32p_row03_traceSegment_096_2733_0017, g32p_row03_traceSegment_096_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2700 33 34, g32p_row03_traceSegment_096_2700_0033, g32p_row03_traceSegment_096_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2767 8 9, g32p_row03_traceSegment_096_2767_0008, g32p_row03_traceSegment_096_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2784 8 9, g32p_row03_traceSegment_096_2784_0008, g32p_row03_traceSegment_096_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2767 17 17, g32p_row03_traceSegment_096_2767_0017, g32p_row03_traceSegment_096_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2801 8 9, g32p_row03_traceSegment_096_2801_0008, g32p_row03_traceSegment_096_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2818 8 9, g32p_row03_traceSegment_096_2818_0008, g32p_row03_traceSegment_096_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2801 17 17, g32p_row03_traceSegment_096_2801_0017, g32p_row03_traceSegment_096_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2767 34 34, g32p_row03_traceSegment_096_2767_0034, g32p_row03_traceSegment_096_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2700 67 68, g32p_row03_traceSegment_096_2700_0067, g32p_row03_traceSegment_096_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2851 8 9, g32p_row03_traceSegment_096_2851_0008, g32p_row03_traceSegment_096_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2835 16 17, g32p_row03_traceSegment_096_2835_0016, g32p_row03_traceSegment_096_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2868 8 9, g32p_row03_traceSegment_096_2868_0008, g32p_row03_traceSegment_096_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2885 8 9, g32p_row03_traceSegment_096_2885_0008, g32p_row03_traceSegment_096_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2868 17 17, g32p_row03_traceSegment_096_2868_0017, g32p_row03_traceSegment_096_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2835 33 34, g32p_row03_traceSegment_096_2835_0033, g32p_row03_traceSegment_096_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2902 8 9, g32p_row03_traceSegment_096_2902_0008, g32p_row03_traceSegment_096_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2919 8 9, g32p_row03_traceSegment_096_2919_0008, g32p_row03_traceSegment_096_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2902 17 17, g32p_row03_traceSegment_096_2902_0017, g32p_row03_traceSegment_096_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2936 8 9, g32p_row03_traceSegment_096_2936_0008, g32p_row03_traceSegment_096_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2953 8 9, g32p_row03_traceSegment_096_2953_0008, g32p_row03_traceSegment_096_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2936 17 17, g32p_row03_traceSegment_096_2936_0017, g32p_row03_traceSegment_096_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2902 34 34, g32p_row03_traceSegment_096_2902_0034, g32p_row03_traceSegment_096_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2835 67 68, g32p_row03_traceSegment_096_2835_0067, g32p_row03_traceSegment_096_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2700 135 135, g32p_row03_traceSegment_096_2700_0135, g32p_row03_traceSegment_096_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2986 8 9, g32p_row03_traceSegment_096_2986_0008, g32p_row03_traceSegment_096_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2970 16 17, g32p_row03_traceSegment_096_2970_0016, g32p_row03_traceSegment_096_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3003 8 9, g32p_row03_traceSegment_096_3003_0008, g32p_row03_traceSegment_096_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3020 8 9, g32p_row03_traceSegment_096_3020_0008, g32p_row03_traceSegment_096_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3003 17 17, g32p_row03_traceSegment_096_3003_0017, g32p_row03_traceSegment_096_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2970 33 34, g32p_row03_traceSegment_096_2970_0033, g32p_row03_traceSegment_096_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3037 8 9, g32p_row03_traceSegment_096_3037_0008, g32p_row03_traceSegment_096_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3054 8 9, g32p_row03_traceSegment_096_3054_0008, g32p_row03_traceSegment_096_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3037 17 17, g32p_row03_traceSegment_096_3037_0017, g32p_row03_traceSegment_096_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3071 8 9, g32p_row03_traceSegment_096_3071_0008, g32p_row03_traceSegment_096_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3088 8 9, g32p_row03_traceSegment_096_3088_0008, g32p_row03_traceSegment_096_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3071 17 17, g32p_row03_traceSegment_096_3071_0017, g32p_row03_traceSegment_096_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3037 34 34, g32p_row03_traceSegment_096_3037_0034, g32p_row03_traceSegment_096_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2970 67 68, g32p_row03_traceSegment_096_2970_0067, g32p_row03_traceSegment_096_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3121 8 9, g32p_row03_traceSegment_096_3121_0008, g32p_row03_traceSegment_096_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3105 16 17, g32p_row03_traceSegment_096_3105_0016, g32p_row03_traceSegment_096_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3138 8 9, g32p_row03_traceSegment_096_3138_0008, g32p_row03_traceSegment_096_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3155 8 9, g32p_row03_traceSegment_096_3155_0008, g32p_row03_traceSegment_096_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3138 17 17, g32p_row03_traceSegment_096_3138_0017, g32p_row03_traceSegment_096_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3105 33 34, g32p_row03_traceSegment_096_3105_0033, g32p_row03_traceSegment_096_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3172 8 9, g32p_row03_traceSegment_096_3172_0008, g32p_row03_traceSegment_096_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3189 8 9, g32p_row03_traceSegment_096_3189_0008, g32p_row03_traceSegment_096_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3172 17 17, g32p_row03_traceSegment_096_3172_0017, g32p_row03_traceSegment_096_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3206 8 9, g32p_row03_traceSegment_096_3206_0008, g32p_row03_traceSegment_096_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3223 8 9, g32p_row03_traceSegment_096_3223_0008, g32p_row03_traceSegment_096_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3206 17 17, g32p_row03_traceSegment_096_3206_0017, g32p_row03_traceSegment_096_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3172 34 34, g32p_row03_traceSegment_096_3172_0034, g32p_row03_traceSegment_096_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3105 67 68, g32p_row03_traceSegment_096_3105_0067, g32p_row03_traceSegment_096_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2970 135 135, g32p_row03_traceSegment_096_2970_0135, g32p_row03_traceSegment_096_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_096 2700 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2700 270 270, g32p_row03_traceSegment_096_2700_0270, g32p_row03_traceSegment_096_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_096 2160 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2160 540 540, g32p_row03_traceSegment_096_2160_0540, g32p_row03_traceSegment_096_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3256 8 9, g32p_row03_traceSegment_096_3256_0008, g32p_row03_traceSegment_096_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3240 16 17, g32p_row03_traceSegment_096_3240_0016, g32p_row03_traceSegment_096_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3273 8 9, g32p_row03_traceSegment_096_3273_0008, g32p_row03_traceSegment_096_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3290 8 9, g32p_row03_traceSegment_096_3290_0008, g32p_row03_traceSegment_096_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3273 17 17, g32p_row03_traceSegment_096_3273_0017, g32p_row03_traceSegment_096_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3240 33 34, g32p_row03_traceSegment_096_3240_0033, g32p_row03_traceSegment_096_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3307 8 9, g32p_row03_traceSegment_096_3307_0008, g32p_row03_traceSegment_096_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3324 8 9, g32p_row03_traceSegment_096_3324_0008, g32p_row03_traceSegment_096_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3307 17 17, g32p_row03_traceSegment_096_3307_0017, g32p_row03_traceSegment_096_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3341 8 9, g32p_row03_traceSegment_096_3341_0008, g32p_row03_traceSegment_096_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3358 8 9, g32p_row03_traceSegment_096_3358_0008, g32p_row03_traceSegment_096_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3341 17 17, g32p_row03_traceSegment_096_3341_0017, g32p_row03_traceSegment_096_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3307 34 34, g32p_row03_traceSegment_096_3307_0034, g32p_row03_traceSegment_096_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3240 67 68, g32p_row03_traceSegment_096_3240_0067, g32p_row03_traceSegment_096_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3391 8 9, g32p_row03_traceSegment_096_3391_0008, g32p_row03_traceSegment_096_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3375 16 17, g32p_row03_traceSegment_096_3375_0016, g32p_row03_traceSegment_096_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3408 8 9, g32p_row03_traceSegment_096_3408_0008, g32p_row03_traceSegment_096_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3425 8 9, g32p_row03_traceSegment_096_3425_0008, g32p_row03_traceSegment_096_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3408 17 17, g32p_row03_traceSegment_096_3408_0017, g32p_row03_traceSegment_096_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3375 33 34, g32p_row03_traceSegment_096_3375_0033, g32p_row03_traceSegment_096_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3442 8 9, g32p_row03_traceSegment_096_3442_0008, g32p_row03_traceSegment_096_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3459 8 9, g32p_row03_traceSegment_096_3459_0008, g32p_row03_traceSegment_096_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3442 17 17, g32p_row03_traceSegment_096_3442_0017, g32p_row03_traceSegment_096_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3476 8 9, g32p_row03_traceSegment_096_3476_0008, g32p_row03_traceSegment_096_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3493 8 9, g32p_row03_traceSegment_096_3493_0008, g32p_row03_traceSegment_096_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3476 17 17, g32p_row03_traceSegment_096_3476_0017, g32p_row03_traceSegment_096_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3442 34 34, g32p_row03_traceSegment_096_3442_0034, g32p_row03_traceSegment_096_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3375 67 68, g32p_row03_traceSegment_096_3375_0067, g32p_row03_traceSegment_096_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3240 135 135, g32p_row03_traceSegment_096_3240_0135, g32p_row03_traceSegment_096_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3526 8 9, g32p_row03_traceSegment_096_3526_0008, g32p_row03_traceSegment_096_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3510 16 17, g32p_row03_traceSegment_096_3510_0016, g32p_row03_traceSegment_096_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3543 8 9, g32p_row03_traceSegment_096_3543_0008, g32p_row03_traceSegment_096_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3560 8 9, g32p_row03_traceSegment_096_3560_0008, g32p_row03_traceSegment_096_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3543 17 17, g32p_row03_traceSegment_096_3543_0017, g32p_row03_traceSegment_096_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3510 33 34, g32p_row03_traceSegment_096_3510_0033, g32p_row03_traceSegment_096_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3577 8 9, g32p_row03_traceSegment_096_3577_0008, g32p_row03_traceSegment_096_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3594 8 9, g32p_row03_traceSegment_096_3594_0008, g32p_row03_traceSegment_096_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3577 17 17, g32p_row03_traceSegment_096_3577_0017, g32p_row03_traceSegment_096_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3611 8 9, g32p_row03_traceSegment_096_3611_0008, g32p_row03_traceSegment_096_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3628 8 9, g32p_row03_traceSegment_096_3628_0008, g32p_row03_traceSegment_096_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3611 17 17, g32p_row03_traceSegment_096_3611_0017, g32p_row03_traceSegment_096_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3577 34 34, g32p_row03_traceSegment_096_3577_0034, g32p_row03_traceSegment_096_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3510 67 68, g32p_row03_traceSegment_096_3510_0067, g32p_row03_traceSegment_096_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3661 8 9, g32p_row03_traceSegment_096_3661_0008, g32p_row03_traceSegment_096_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3645 16 17, g32p_row03_traceSegment_096_3645_0016, g32p_row03_traceSegment_096_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3678 8 9, g32p_row03_traceSegment_096_3678_0008, g32p_row03_traceSegment_096_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3695 8 9, g32p_row03_traceSegment_096_3695_0008, g32p_row03_traceSegment_096_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3678 17 17, g32p_row03_traceSegment_096_3678_0017, g32p_row03_traceSegment_096_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3645 33 34, g32p_row03_traceSegment_096_3645_0033, g32p_row03_traceSegment_096_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3712 8 9, g32p_row03_traceSegment_096_3712_0008, g32p_row03_traceSegment_096_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3729 8 9, g32p_row03_traceSegment_096_3729_0008, g32p_row03_traceSegment_096_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3712 17 17, g32p_row03_traceSegment_096_3712_0017, g32p_row03_traceSegment_096_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3746 8 9, g32p_row03_traceSegment_096_3746_0008, g32p_row03_traceSegment_096_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3763 8 9, g32p_row03_traceSegment_096_3763_0008, g32p_row03_traceSegment_096_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3746 17 17, g32p_row03_traceSegment_096_3746_0017, g32p_row03_traceSegment_096_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3712 34 34, g32p_row03_traceSegment_096_3712_0034, g32p_row03_traceSegment_096_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3645 67 68, g32p_row03_traceSegment_096_3645_0067, g32p_row03_traceSegment_096_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 3510 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3510 135 135, g32p_row03_traceSegment_096_3510_0135, g32p_row03_traceSegment_096_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_096 3240 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3240 270 270, g32p_row03_traceSegment_096_3240_0270, g32p_row03_traceSegment_096_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3796 8 9, g32p_row03_traceSegment_096_3796_0008, g32p_row03_traceSegment_096_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3780 16 17, g32p_row03_traceSegment_096_3780_0016, g32p_row03_traceSegment_096_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3813 8 9, g32p_row03_traceSegment_096_3813_0008, g32p_row03_traceSegment_096_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3830 8 9, g32p_row03_traceSegment_096_3830_0008, g32p_row03_traceSegment_096_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3813 17 17, g32p_row03_traceSegment_096_3813_0017, g32p_row03_traceSegment_096_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3780 33 34, g32p_row03_traceSegment_096_3780_0033, g32p_row03_traceSegment_096_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3847 8 9, g32p_row03_traceSegment_096_3847_0008, g32p_row03_traceSegment_096_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3864 8 9, g32p_row03_traceSegment_096_3864_0008, g32p_row03_traceSegment_096_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3847 17 17, g32p_row03_traceSegment_096_3847_0017, g32p_row03_traceSegment_096_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3881 8 9, g32p_row03_traceSegment_096_3881_0008, g32p_row03_traceSegment_096_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3898 8 9, g32p_row03_traceSegment_096_3898_0008, g32p_row03_traceSegment_096_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3881 17 17, g32p_row03_traceSegment_096_3881_0017, g32p_row03_traceSegment_096_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3847 34 34, g32p_row03_traceSegment_096_3847_0034, g32p_row03_traceSegment_096_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3780 67 68, g32p_row03_traceSegment_096_3780_0067, g32p_row03_traceSegment_096_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3931 8 9, g32p_row03_traceSegment_096_3931_0008, g32p_row03_traceSegment_096_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3915 16 17, g32p_row03_traceSegment_096_3915_0016, g32p_row03_traceSegment_096_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3948 8 9, g32p_row03_traceSegment_096_3948_0008, g32p_row03_traceSegment_096_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3965 8 9, g32p_row03_traceSegment_096_3965_0008, g32p_row03_traceSegment_096_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3948 17 17, g32p_row03_traceSegment_096_3948_0017, g32p_row03_traceSegment_096_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3915 33 34, g32p_row03_traceSegment_096_3915_0033, g32p_row03_traceSegment_096_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3982 8 9, g32p_row03_traceSegment_096_3982_0008, g32p_row03_traceSegment_096_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3999 8 9, g32p_row03_traceSegment_096_3999_0008, g32p_row03_traceSegment_096_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3982 17 17, g32p_row03_traceSegment_096_3982_0017, g32p_row03_traceSegment_096_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4016 8 9, g32p_row03_traceSegment_096_4016_0008, g32p_row03_traceSegment_096_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4033 8 9, g32p_row03_traceSegment_096_4033_0008, g32p_row03_traceSegment_096_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4016 17 17, g32p_row03_traceSegment_096_4016_0017, g32p_row03_traceSegment_096_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3982 34 34, g32p_row03_traceSegment_096_3982_0034, g32p_row03_traceSegment_096_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3915 67 68, g32p_row03_traceSegment_096_3915_0067, g32p_row03_traceSegment_096_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3780 135 135, g32p_row03_traceSegment_096_3780_0135, g32p_row03_traceSegment_096_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4066 8 9, g32p_row03_traceSegment_096_4066_0008, g32p_row03_traceSegment_096_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4050 16 17, g32p_row03_traceSegment_096_4050_0016, g32p_row03_traceSegment_096_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4083 8 9, g32p_row03_traceSegment_096_4083_0008, g32p_row03_traceSegment_096_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4100 8 9, g32p_row03_traceSegment_096_4100_0008, g32p_row03_traceSegment_096_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4083 17 17, g32p_row03_traceSegment_096_4083_0017, g32p_row03_traceSegment_096_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4050 33 34, g32p_row03_traceSegment_096_4050_0033, g32p_row03_traceSegment_096_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4117 8 9, g32p_row03_traceSegment_096_4117_0008, g32p_row03_traceSegment_096_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4134 8 9, g32p_row03_traceSegment_096_4134_0008, g32p_row03_traceSegment_096_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4117 17 17, g32p_row03_traceSegment_096_4117_0017, g32p_row03_traceSegment_096_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4151 8 9, g32p_row03_traceSegment_096_4151_0008, g32p_row03_traceSegment_096_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4168 8 9, g32p_row03_traceSegment_096_4168_0008, g32p_row03_traceSegment_096_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4151 17 17, g32p_row03_traceSegment_096_4151_0017, g32p_row03_traceSegment_096_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4117 34 34, g32p_row03_traceSegment_096_4117_0034, g32p_row03_traceSegment_096_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4050 67 68, g32p_row03_traceSegment_096_4050_0067, g32p_row03_traceSegment_096_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_096 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4201 8 9, g32p_row03_traceSegment_096_4201_0008, g32p_row03_traceSegment_096_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_096 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4185 16 17, g32p_row03_traceSegment_096_4185_0016, g32p_row03_traceSegment_096_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4218 8 9, g32p_row03_traceSegment_096_4218_0008, g32p_row03_traceSegment_096_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4235 8 9, g32p_row03_traceSegment_096_4235_0008, g32p_row03_traceSegment_096_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4218 17 17, g32p_row03_traceSegment_096_4218_0017, g32p_row03_traceSegment_096_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_096 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4185 33 34, g32p_row03_traceSegment_096_4185_0033, g32p_row03_traceSegment_096_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4252 8 9, g32p_row03_traceSegment_096_4252_0008, g32p_row03_traceSegment_096_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4269 8 9, g32p_row03_traceSegment_096_4269_0008, g32p_row03_traceSegment_096_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4252 17 17, g32p_row03_traceSegment_096_4252_0017, g32p_row03_traceSegment_096_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4286 8 9, g32p_row03_traceSegment_096_4286_0008, g32p_row03_traceSegment_096_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_096 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_096 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_096_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_096 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4303 8 9, g32p_row03_traceSegment_096_4303_0008, g32p_row03_traceSegment_096_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_096 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4286 17 17, g32p_row03_traceSegment_096_4286_0017, g32p_row03_traceSegment_096_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_096 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4252 34 34, g32p_row03_traceSegment_096_4252_0034, g32p_row03_traceSegment_096_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_096 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4185 67 68, g32p_row03_traceSegment_096_4185_0067, g32p_row03_traceSegment_096_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_096_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_096 4050 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 4050 135 135, g32p_row03_traceSegment_096_4050_0135, g32p_row03_traceSegment_096_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_096 3780 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3780 270 270, g32p_row03_traceSegment_096_3780_0270, g32p_row03_traceSegment_096_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_096_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_096 3240 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 3240 540 540, g32p_row03_traceSegment_096_3240_0540, g32p_row03_traceSegment_096_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_096_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_096 2160 2160 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 2160 1080 1080, g32p_row03_traceSegment_096_2160_1080, g32p_row03_traceSegment_096_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_096_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_096 0 4320 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_096 0 2160 2160, g32p_row03_traceSegment_096_0000_2160, g32p_row03_traceSegment_096_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 96 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_096_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_097_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 24 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 16 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 16 8 9, g32p_row03_traceSegment_097_0016_0008, g32p_row03_traceSegment_097_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 0 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 0 16 17, g32p_row03_traceSegment_097_0000_0016, g32p_row03_traceSegment_097_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 33 8 9, g32p_row03_traceSegment_097_0033_0008, g32p_row03_traceSegment_097_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 50 8 9, g32p_row03_traceSegment_097_0050_0008, g32p_row03_traceSegment_097_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 33 17 17, g32p_row03_traceSegment_097_0033_0017, g32p_row03_traceSegment_097_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 0 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 0 33 34, g32p_row03_traceSegment_097_0000_0033, g32p_row03_traceSegment_097_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 67 8 9, g32p_row03_traceSegment_097_0067_0008, g32p_row03_traceSegment_097_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 84 8 9, g32p_row03_traceSegment_097_0084_0008, g32p_row03_traceSegment_097_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 67 17 17, g32p_row03_traceSegment_097_0067_0017, g32p_row03_traceSegment_097_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 101 8 9, g32p_row03_traceSegment_097_0101_0008, g32p_row03_traceSegment_097_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 118 8 9, g32p_row03_traceSegment_097_0118_0008, g32p_row03_traceSegment_097_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 101 17 17, g32p_row03_traceSegment_097_0101_0017, g32p_row03_traceSegment_097_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 67 34 34, g32p_row03_traceSegment_097_0067_0034, g32p_row03_traceSegment_097_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 0 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 0 67 68, g32p_row03_traceSegment_097_0000_0067, g32p_row03_traceSegment_097_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 151 8 9, g32p_row03_traceSegment_097_0151_0008, g32p_row03_traceSegment_097_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 135 16 17, g32p_row03_traceSegment_097_0135_0016, g32p_row03_traceSegment_097_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 168 8 9, g32p_row03_traceSegment_097_0168_0008, g32p_row03_traceSegment_097_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 185 8 9, g32p_row03_traceSegment_097_0185_0008, g32p_row03_traceSegment_097_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 168 17 17, g32p_row03_traceSegment_097_0168_0017, g32p_row03_traceSegment_097_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 135 33 34, g32p_row03_traceSegment_097_0135_0033, g32p_row03_traceSegment_097_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 202 8 9, g32p_row03_traceSegment_097_0202_0008, g32p_row03_traceSegment_097_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 219 8 9, g32p_row03_traceSegment_097_0219_0008, g32p_row03_traceSegment_097_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 202 17 17, g32p_row03_traceSegment_097_0202_0017, g32p_row03_traceSegment_097_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 236 8 9, g32p_row03_traceSegment_097_0236_0008, g32p_row03_traceSegment_097_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 253 8 9, g32p_row03_traceSegment_097_0253_0008, g32p_row03_traceSegment_097_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 236 17 17, g32p_row03_traceSegment_097_0236_0017, g32p_row03_traceSegment_097_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 202 34 34, g32p_row03_traceSegment_097_0202_0034, g32p_row03_traceSegment_097_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 135 67 68, g32p_row03_traceSegment_097_0135_0067, g32p_row03_traceSegment_097_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 0 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 0 135 135, g32p_row03_traceSegment_097_0000_0135, g32p_row03_traceSegment_097_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 286 8 9, g32p_row03_traceSegment_097_0286_0008, g32p_row03_traceSegment_097_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 270 16 17, g32p_row03_traceSegment_097_0270_0016, g32p_row03_traceSegment_097_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 303 8 9, g32p_row03_traceSegment_097_0303_0008, g32p_row03_traceSegment_097_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 320 8 9, g32p_row03_traceSegment_097_0320_0008, g32p_row03_traceSegment_097_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 303 17 17, g32p_row03_traceSegment_097_0303_0017, g32p_row03_traceSegment_097_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 270 33 34, g32p_row03_traceSegment_097_0270_0033, g32p_row03_traceSegment_097_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 337 8 9, g32p_row03_traceSegment_097_0337_0008, g32p_row03_traceSegment_097_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 354 8 9, g32p_row03_traceSegment_097_0354_0008, g32p_row03_traceSegment_097_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 337 17 17, g32p_row03_traceSegment_097_0337_0017, g32p_row03_traceSegment_097_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 371 8 9, g32p_row03_traceSegment_097_0371_0008, g32p_row03_traceSegment_097_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 388 8 9, g32p_row03_traceSegment_097_0388_0008, g32p_row03_traceSegment_097_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 371 17 17, g32p_row03_traceSegment_097_0371_0017, g32p_row03_traceSegment_097_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 337 34 34, g32p_row03_traceSegment_097_0337_0034, g32p_row03_traceSegment_097_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 270 67 68, g32p_row03_traceSegment_097_0270_0067, g32p_row03_traceSegment_097_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 421 8 9, g32p_row03_traceSegment_097_0421_0008, g32p_row03_traceSegment_097_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 405 16 17, g32p_row03_traceSegment_097_0405_0016, g32p_row03_traceSegment_097_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 438 8 9, g32p_row03_traceSegment_097_0438_0008, g32p_row03_traceSegment_097_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 455 8 9, g32p_row03_traceSegment_097_0455_0008, g32p_row03_traceSegment_097_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 438 17 17, g32p_row03_traceSegment_097_0438_0017, g32p_row03_traceSegment_097_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 405 33 34, g32p_row03_traceSegment_097_0405_0033, g32p_row03_traceSegment_097_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 472 8 9, g32p_row03_traceSegment_097_0472_0008, g32p_row03_traceSegment_097_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 489 8 9, g32p_row03_traceSegment_097_0489_0008, g32p_row03_traceSegment_097_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 472 17 17, g32p_row03_traceSegment_097_0472_0017, g32p_row03_traceSegment_097_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 506 8 9, g32p_row03_traceSegment_097_0506_0008, g32p_row03_traceSegment_097_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 523 8 9, g32p_row03_traceSegment_097_0523_0008, g32p_row03_traceSegment_097_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 506 17 17, g32p_row03_traceSegment_097_0506_0017, g32p_row03_traceSegment_097_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 472 34 34, g32p_row03_traceSegment_097_0472_0034, g32p_row03_traceSegment_097_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 405 67 68, g32p_row03_traceSegment_097_0405_0067, g32p_row03_traceSegment_097_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 270 135 135, g32p_row03_traceSegment_097_0270_0135, g32p_row03_traceSegment_097_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_097 0 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 0 270 270, g32p_row03_traceSegment_097_0000_0270, g32p_row03_traceSegment_097_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 556 8 9, g32p_row03_traceSegment_097_0556_0008, g32p_row03_traceSegment_097_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 540 16 17, g32p_row03_traceSegment_097_0540_0016, g32p_row03_traceSegment_097_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 573 8 9, g32p_row03_traceSegment_097_0573_0008, g32p_row03_traceSegment_097_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 590 8 9, g32p_row03_traceSegment_097_0590_0008, g32p_row03_traceSegment_097_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 573 17 17, g32p_row03_traceSegment_097_0573_0017, g32p_row03_traceSegment_097_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 540 33 34, g32p_row03_traceSegment_097_0540_0033, g32p_row03_traceSegment_097_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 607 8 9, g32p_row03_traceSegment_097_0607_0008, g32p_row03_traceSegment_097_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 624 8 9, g32p_row03_traceSegment_097_0624_0008, g32p_row03_traceSegment_097_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 607 17 17, g32p_row03_traceSegment_097_0607_0017, g32p_row03_traceSegment_097_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 641 8 9, g32p_row03_traceSegment_097_0641_0008, g32p_row03_traceSegment_097_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 658 8 9, g32p_row03_traceSegment_097_0658_0008, g32p_row03_traceSegment_097_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 641 17 17, g32p_row03_traceSegment_097_0641_0017, g32p_row03_traceSegment_097_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 607 34 34, g32p_row03_traceSegment_097_0607_0034, g32p_row03_traceSegment_097_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 540 67 68, g32p_row03_traceSegment_097_0540_0067, g32p_row03_traceSegment_097_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 691 8 9, g32p_row03_traceSegment_097_0691_0008, g32p_row03_traceSegment_097_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 675 16 17, g32p_row03_traceSegment_097_0675_0016, g32p_row03_traceSegment_097_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 708 8 9, g32p_row03_traceSegment_097_0708_0008, g32p_row03_traceSegment_097_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 725 8 9, g32p_row03_traceSegment_097_0725_0008, g32p_row03_traceSegment_097_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 708 17 17, g32p_row03_traceSegment_097_0708_0017, g32p_row03_traceSegment_097_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 675 33 34, g32p_row03_traceSegment_097_0675_0033, g32p_row03_traceSegment_097_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 742 8 9, g32p_row03_traceSegment_097_0742_0008, g32p_row03_traceSegment_097_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 759 8 9, g32p_row03_traceSegment_097_0759_0008, g32p_row03_traceSegment_097_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 742 17 17, g32p_row03_traceSegment_097_0742_0017, g32p_row03_traceSegment_097_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 776 8 9, g32p_row03_traceSegment_097_0776_0008, g32p_row03_traceSegment_097_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 793 8 9, g32p_row03_traceSegment_097_0793_0008, g32p_row03_traceSegment_097_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 776 17 17, g32p_row03_traceSegment_097_0776_0017, g32p_row03_traceSegment_097_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 742 34 34, g32p_row03_traceSegment_097_0742_0034, g32p_row03_traceSegment_097_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 675 67 68, g32p_row03_traceSegment_097_0675_0067, g32p_row03_traceSegment_097_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 540 135 135, g32p_row03_traceSegment_097_0540_0135, g32p_row03_traceSegment_097_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 826 8 9, g32p_row03_traceSegment_097_0826_0008, g32p_row03_traceSegment_097_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 810 16 17, g32p_row03_traceSegment_097_0810_0016, g32p_row03_traceSegment_097_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 843 8 9, g32p_row03_traceSegment_097_0843_0008, g32p_row03_traceSegment_097_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 860 8 9, g32p_row03_traceSegment_097_0860_0008, g32p_row03_traceSegment_097_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 843 17 17, g32p_row03_traceSegment_097_0843_0017, g32p_row03_traceSegment_097_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 810 33 34, g32p_row03_traceSegment_097_0810_0033, g32p_row03_traceSegment_097_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 877 8 9, g32p_row03_traceSegment_097_0877_0008, g32p_row03_traceSegment_097_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 894 8 9, g32p_row03_traceSegment_097_0894_0008, g32p_row03_traceSegment_097_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 877 17 17, g32p_row03_traceSegment_097_0877_0017, g32p_row03_traceSegment_097_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 911 8 9, g32p_row03_traceSegment_097_0911_0008, g32p_row03_traceSegment_097_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 928 8 9, g32p_row03_traceSegment_097_0928_0008, g32p_row03_traceSegment_097_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 911 17 17, g32p_row03_traceSegment_097_0911_0017, g32p_row03_traceSegment_097_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 877 34 34, g32p_row03_traceSegment_097_0877_0034, g32p_row03_traceSegment_097_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 810 67 68, g32p_row03_traceSegment_097_0810_0067, g32p_row03_traceSegment_097_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 961 8 9, g32p_row03_traceSegment_097_0961_0008, g32p_row03_traceSegment_097_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 945 16 17, g32p_row03_traceSegment_097_0945_0016, g32p_row03_traceSegment_097_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 978 8 9, g32p_row03_traceSegment_097_0978_0008, g32p_row03_traceSegment_097_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 995 8 9, g32p_row03_traceSegment_097_0995_0008, g32p_row03_traceSegment_097_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 978 17 17, g32p_row03_traceSegment_097_0978_0017, g32p_row03_traceSegment_097_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 945 33 34, g32p_row03_traceSegment_097_0945_0033, g32p_row03_traceSegment_097_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1012 8 9, g32p_row03_traceSegment_097_1012_0008, g32p_row03_traceSegment_097_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1029 8 9, g32p_row03_traceSegment_097_1029_0008, g32p_row03_traceSegment_097_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1012 17 17, g32p_row03_traceSegment_097_1012_0017, g32p_row03_traceSegment_097_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1046 8 9, g32p_row03_traceSegment_097_1046_0008, g32p_row03_traceSegment_097_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1063 8 9, g32p_row03_traceSegment_097_1063_0008, g32p_row03_traceSegment_097_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1046 17 17, g32p_row03_traceSegment_097_1046_0017, g32p_row03_traceSegment_097_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1012 34 34, g32p_row03_traceSegment_097_1012_0034, g32p_row03_traceSegment_097_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 945 67 68, g32p_row03_traceSegment_097_0945_0067, g32p_row03_traceSegment_097_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 810 135 135, g32p_row03_traceSegment_097_0810_0135, g32p_row03_traceSegment_097_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_097 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 540 270 270, g32p_row03_traceSegment_097_0540_0270, g32p_row03_traceSegment_097_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_097 0 1080 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 0 540 540, g32p_row03_traceSegment_097_0000_0540, g32p_row03_traceSegment_097_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1096 8 9, g32p_row03_traceSegment_097_1096_0008, g32p_row03_traceSegment_097_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1080 16 17, g32p_row03_traceSegment_097_1080_0016, g32p_row03_traceSegment_097_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1113 8 9, g32p_row03_traceSegment_097_1113_0008, g32p_row03_traceSegment_097_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1130 8 9, g32p_row03_traceSegment_097_1130_0008, g32p_row03_traceSegment_097_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1113 17 17, g32p_row03_traceSegment_097_1113_0017, g32p_row03_traceSegment_097_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1080 33 34, g32p_row03_traceSegment_097_1080_0033, g32p_row03_traceSegment_097_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1147 8 9, g32p_row03_traceSegment_097_1147_0008, g32p_row03_traceSegment_097_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1164 8 9, g32p_row03_traceSegment_097_1164_0008, g32p_row03_traceSegment_097_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1147 17 17, g32p_row03_traceSegment_097_1147_0017, g32p_row03_traceSegment_097_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1181 8 9, g32p_row03_traceSegment_097_1181_0008, g32p_row03_traceSegment_097_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1198 8 9, g32p_row03_traceSegment_097_1198_0008, g32p_row03_traceSegment_097_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1181 17 17, g32p_row03_traceSegment_097_1181_0017, g32p_row03_traceSegment_097_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1147 34 34, g32p_row03_traceSegment_097_1147_0034, g32p_row03_traceSegment_097_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1080 67 68, g32p_row03_traceSegment_097_1080_0067, g32p_row03_traceSegment_097_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1231 8 9, g32p_row03_traceSegment_097_1231_0008, g32p_row03_traceSegment_097_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1215 16 17, g32p_row03_traceSegment_097_1215_0016, g32p_row03_traceSegment_097_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1248 8 9, g32p_row03_traceSegment_097_1248_0008, g32p_row03_traceSegment_097_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1265 8 9, g32p_row03_traceSegment_097_1265_0008, g32p_row03_traceSegment_097_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1248 17 17, g32p_row03_traceSegment_097_1248_0017, g32p_row03_traceSegment_097_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1215 33 34, g32p_row03_traceSegment_097_1215_0033, g32p_row03_traceSegment_097_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1282 8 9, g32p_row03_traceSegment_097_1282_0008, g32p_row03_traceSegment_097_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1299 8 9, g32p_row03_traceSegment_097_1299_0008, g32p_row03_traceSegment_097_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1282 17 17, g32p_row03_traceSegment_097_1282_0017, g32p_row03_traceSegment_097_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1316 8 9, g32p_row03_traceSegment_097_1316_0008, g32p_row03_traceSegment_097_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1333 8 9, g32p_row03_traceSegment_097_1333_0008, g32p_row03_traceSegment_097_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1316 17 17, g32p_row03_traceSegment_097_1316_0017, g32p_row03_traceSegment_097_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1282 34 34, g32p_row03_traceSegment_097_1282_0034, g32p_row03_traceSegment_097_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1215 67 68, g32p_row03_traceSegment_097_1215_0067, g32p_row03_traceSegment_097_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1080 135 135, g32p_row03_traceSegment_097_1080_0135, g32p_row03_traceSegment_097_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1366 8 9, g32p_row03_traceSegment_097_1366_0008, g32p_row03_traceSegment_097_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1350 16 17, g32p_row03_traceSegment_097_1350_0016, g32p_row03_traceSegment_097_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1383 8 9, g32p_row03_traceSegment_097_1383_0008, g32p_row03_traceSegment_097_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1400 8 9, g32p_row03_traceSegment_097_1400_0008, g32p_row03_traceSegment_097_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1383 17 17, g32p_row03_traceSegment_097_1383_0017, g32p_row03_traceSegment_097_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1350 33 34, g32p_row03_traceSegment_097_1350_0033, g32p_row03_traceSegment_097_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1417 8 9, g32p_row03_traceSegment_097_1417_0008, g32p_row03_traceSegment_097_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1434 8 9, g32p_row03_traceSegment_097_1434_0008, g32p_row03_traceSegment_097_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1417 17 17, g32p_row03_traceSegment_097_1417_0017, g32p_row03_traceSegment_097_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1451 8 9, g32p_row03_traceSegment_097_1451_0008, g32p_row03_traceSegment_097_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1468 8 9, g32p_row03_traceSegment_097_1468_0008, g32p_row03_traceSegment_097_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1451 17 17, g32p_row03_traceSegment_097_1451_0017, g32p_row03_traceSegment_097_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1417 34 34, g32p_row03_traceSegment_097_1417_0034, g32p_row03_traceSegment_097_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1350 67 68, g32p_row03_traceSegment_097_1350_0067, g32p_row03_traceSegment_097_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1501 8 9, g32p_row03_traceSegment_097_1501_0008, g32p_row03_traceSegment_097_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1485 16 17, g32p_row03_traceSegment_097_1485_0016, g32p_row03_traceSegment_097_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1518 8 9, g32p_row03_traceSegment_097_1518_0008, g32p_row03_traceSegment_097_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1535 8 9, g32p_row03_traceSegment_097_1535_0008, g32p_row03_traceSegment_097_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1518 17 17, g32p_row03_traceSegment_097_1518_0017, g32p_row03_traceSegment_097_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1485 33 34, g32p_row03_traceSegment_097_1485_0033, g32p_row03_traceSegment_097_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1552 8 9, g32p_row03_traceSegment_097_1552_0008, g32p_row03_traceSegment_097_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1569 8 9, g32p_row03_traceSegment_097_1569_0008, g32p_row03_traceSegment_097_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1552 17 17, g32p_row03_traceSegment_097_1552_0017, g32p_row03_traceSegment_097_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1586 8 9, g32p_row03_traceSegment_097_1586_0008, g32p_row03_traceSegment_097_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1603 8 9, g32p_row03_traceSegment_097_1603_0008, g32p_row03_traceSegment_097_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1586 17 17, g32p_row03_traceSegment_097_1586_0017, g32p_row03_traceSegment_097_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1552 34 34, g32p_row03_traceSegment_097_1552_0034, g32p_row03_traceSegment_097_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1485 67 68, g32p_row03_traceSegment_097_1485_0067, g32p_row03_traceSegment_097_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1350 135 135, g32p_row03_traceSegment_097_1350_0135, g32p_row03_traceSegment_097_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_097 1080 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1080 270 270, g32p_row03_traceSegment_097_1080_0270, g32p_row03_traceSegment_097_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1636 8 9, g32p_row03_traceSegment_097_1636_0008, g32p_row03_traceSegment_097_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1620 16 17, g32p_row03_traceSegment_097_1620_0016, g32p_row03_traceSegment_097_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1653 8 9, g32p_row03_traceSegment_097_1653_0008, g32p_row03_traceSegment_097_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1670 8 9, g32p_row03_traceSegment_097_1670_0008, g32p_row03_traceSegment_097_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1653 17 17, g32p_row03_traceSegment_097_1653_0017, g32p_row03_traceSegment_097_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1620 33 34, g32p_row03_traceSegment_097_1620_0033, g32p_row03_traceSegment_097_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1687 8 9, g32p_row03_traceSegment_097_1687_0008, g32p_row03_traceSegment_097_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1704 8 9, g32p_row03_traceSegment_097_1704_0008, g32p_row03_traceSegment_097_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1687 17 17, g32p_row03_traceSegment_097_1687_0017, g32p_row03_traceSegment_097_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1721 8 9, g32p_row03_traceSegment_097_1721_0008, g32p_row03_traceSegment_097_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1738 8 9, g32p_row03_traceSegment_097_1738_0008, g32p_row03_traceSegment_097_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1721 17 17, g32p_row03_traceSegment_097_1721_0017, g32p_row03_traceSegment_097_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1687 34 34, g32p_row03_traceSegment_097_1687_0034, g32p_row03_traceSegment_097_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1620 67 68, g32p_row03_traceSegment_097_1620_0067, g32p_row03_traceSegment_097_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1771 8 9, g32p_row03_traceSegment_097_1771_0008, g32p_row03_traceSegment_097_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1755 16 17, g32p_row03_traceSegment_097_1755_0016, g32p_row03_traceSegment_097_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1788 8 9, g32p_row03_traceSegment_097_1788_0008, g32p_row03_traceSegment_097_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1805 8 9, g32p_row03_traceSegment_097_1805_0008, g32p_row03_traceSegment_097_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1788 17 17, g32p_row03_traceSegment_097_1788_0017, g32p_row03_traceSegment_097_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1755 33 34, g32p_row03_traceSegment_097_1755_0033, g32p_row03_traceSegment_097_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1822 8 9, g32p_row03_traceSegment_097_1822_0008, g32p_row03_traceSegment_097_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1839 8 9, g32p_row03_traceSegment_097_1839_0008, g32p_row03_traceSegment_097_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1822 17 17, g32p_row03_traceSegment_097_1822_0017, g32p_row03_traceSegment_097_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1856 8 9, g32p_row03_traceSegment_097_1856_0008, g32p_row03_traceSegment_097_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1873 8 9, g32p_row03_traceSegment_097_1873_0008, g32p_row03_traceSegment_097_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1856 17 17, g32p_row03_traceSegment_097_1856_0017, g32p_row03_traceSegment_097_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1822 34 34, g32p_row03_traceSegment_097_1822_0034, g32p_row03_traceSegment_097_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1755 67 68, g32p_row03_traceSegment_097_1755_0067, g32p_row03_traceSegment_097_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1620 135 135, g32p_row03_traceSegment_097_1620_0135, g32p_row03_traceSegment_097_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1906 8 9, g32p_row03_traceSegment_097_1906_0008, g32p_row03_traceSegment_097_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1890 16 17, g32p_row03_traceSegment_097_1890_0016, g32p_row03_traceSegment_097_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1923 8 9, g32p_row03_traceSegment_097_1923_0008, g32p_row03_traceSegment_097_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1940 8 9, g32p_row03_traceSegment_097_1940_0008, g32p_row03_traceSegment_097_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1923 17 17, g32p_row03_traceSegment_097_1923_0017, g32p_row03_traceSegment_097_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1890 33 34, g32p_row03_traceSegment_097_1890_0033, g32p_row03_traceSegment_097_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1957 8 9, g32p_row03_traceSegment_097_1957_0008, g32p_row03_traceSegment_097_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1974 8 9, g32p_row03_traceSegment_097_1974_0008, g32p_row03_traceSegment_097_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1957 17 17, g32p_row03_traceSegment_097_1957_0017, g32p_row03_traceSegment_097_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1991 8 9, g32p_row03_traceSegment_097_1991_0008, g32p_row03_traceSegment_097_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2008 8 9, g32p_row03_traceSegment_097_2008_0008, g32p_row03_traceSegment_097_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1991 17 17, g32p_row03_traceSegment_097_1991_0017, g32p_row03_traceSegment_097_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1957 34 34, g32p_row03_traceSegment_097_1957_0034, g32p_row03_traceSegment_097_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1890 67 68, g32p_row03_traceSegment_097_1890_0067, g32p_row03_traceSegment_097_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2041 8 9, g32p_row03_traceSegment_097_2041_0008, g32p_row03_traceSegment_097_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2025 16 17, g32p_row03_traceSegment_097_2025_0016, g32p_row03_traceSegment_097_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2058 8 9, g32p_row03_traceSegment_097_2058_0008, g32p_row03_traceSegment_097_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2075 8 9, g32p_row03_traceSegment_097_2075_0008, g32p_row03_traceSegment_097_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2058 17 17, g32p_row03_traceSegment_097_2058_0017, g32p_row03_traceSegment_097_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2025 33 34, g32p_row03_traceSegment_097_2025_0033, g32p_row03_traceSegment_097_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2092 8 9, g32p_row03_traceSegment_097_2092_0008, g32p_row03_traceSegment_097_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2109 8 9, g32p_row03_traceSegment_097_2109_0008, g32p_row03_traceSegment_097_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2092 17 17, g32p_row03_traceSegment_097_2092_0017, g32p_row03_traceSegment_097_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2126 8 9, g32p_row03_traceSegment_097_2126_0008, g32p_row03_traceSegment_097_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2143 8 9, g32p_row03_traceSegment_097_2143_0008, g32p_row03_traceSegment_097_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2126 17 17, g32p_row03_traceSegment_097_2126_0017, g32p_row03_traceSegment_097_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2092 34 34, g32p_row03_traceSegment_097_2092_0034, g32p_row03_traceSegment_097_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2025 67 68, g32p_row03_traceSegment_097_2025_0067, g32p_row03_traceSegment_097_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 1890 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1890 135 135, g32p_row03_traceSegment_097_1890_0135, g32p_row03_traceSegment_097_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_097 1620 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1620 270 270, g32p_row03_traceSegment_097_1620_0270, g32p_row03_traceSegment_097_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_097_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_097 1080 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 1080 540 540, g32p_row03_traceSegment_097_1080_0540, g32p_row03_traceSegment_097_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_097 0 2160 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 0 1080 1080, g32p_row03_traceSegment_097_0000_1080, g32p_row03_traceSegment_097_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2176 8 9, g32p_row03_traceSegment_097_2176_0008, g32p_row03_traceSegment_097_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2160 16 17, g32p_row03_traceSegment_097_2160_0016, g32p_row03_traceSegment_097_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2193 8 9, g32p_row03_traceSegment_097_2193_0008, g32p_row03_traceSegment_097_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2210 8 9, g32p_row03_traceSegment_097_2210_0008, g32p_row03_traceSegment_097_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2193 17 17, g32p_row03_traceSegment_097_2193_0017, g32p_row03_traceSegment_097_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2160 33 34, g32p_row03_traceSegment_097_2160_0033, g32p_row03_traceSegment_097_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2227 8 9, g32p_row03_traceSegment_097_2227_0008, g32p_row03_traceSegment_097_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2244 8 9, g32p_row03_traceSegment_097_2244_0008, g32p_row03_traceSegment_097_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2227 17 17, g32p_row03_traceSegment_097_2227_0017, g32p_row03_traceSegment_097_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2261 8 9, g32p_row03_traceSegment_097_2261_0008, g32p_row03_traceSegment_097_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2278 8 9, g32p_row03_traceSegment_097_2278_0008, g32p_row03_traceSegment_097_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2261 17 17, g32p_row03_traceSegment_097_2261_0017, g32p_row03_traceSegment_097_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2227 34 34, g32p_row03_traceSegment_097_2227_0034, g32p_row03_traceSegment_097_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2160 67 68, g32p_row03_traceSegment_097_2160_0067, g32p_row03_traceSegment_097_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2311 8 9, g32p_row03_traceSegment_097_2311_0008, g32p_row03_traceSegment_097_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2295 16 17, g32p_row03_traceSegment_097_2295_0016, g32p_row03_traceSegment_097_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2328 8 9, g32p_row03_traceSegment_097_2328_0008, g32p_row03_traceSegment_097_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2345 8 9, g32p_row03_traceSegment_097_2345_0008, g32p_row03_traceSegment_097_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2328 17 17, g32p_row03_traceSegment_097_2328_0017, g32p_row03_traceSegment_097_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2295 33 34, g32p_row03_traceSegment_097_2295_0033, g32p_row03_traceSegment_097_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2362 8 9, g32p_row03_traceSegment_097_2362_0008, g32p_row03_traceSegment_097_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2379 8 9, g32p_row03_traceSegment_097_2379_0008, g32p_row03_traceSegment_097_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2362 17 17, g32p_row03_traceSegment_097_2362_0017, g32p_row03_traceSegment_097_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2396 8 9, g32p_row03_traceSegment_097_2396_0008, g32p_row03_traceSegment_097_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2413 8 9, g32p_row03_traceSegment_097_2413_0008, g32p_row03_traceSegment_097_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2396 17 17, g32p_row03_traceSegment_097_2396_0017, g32p_row03_traceSegment_097_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2362 34 34, g32p_row03_traceSegment_097_2362_0034, g32p_row03_traceSegment_097_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2295 67 68, g32p_row03_traceSegment_097_2295_0067, g32p_row03_traceSegment_097_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 2160 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2160 135 135, g32p_row03_traceSegment_097_2160_0135, g32p_row03_traceSegment_097_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2446 8 9, g32p_row03_traceSegment_097_2446_0008, g32p_row03_traceSegment_097_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2430 16 17, g32p_row03_traceSegment_097_2430_0016, g32p_row03_traceSegment_097_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2463 8 9, g32p_row03_traceSegment_097_2463_0008, g32p_row03_traceSegment_097_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2480 8 9, g32p_row03_traceSegment_097_2480_0008, g32p_row03_traceSegment_097_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2463 17 17, g32p_row03_traceSegment_097_2463_0017, g32p_row03_traceSegment_097_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2430 33 34, g32p_row03_traceSegment_097_2430_0033, g32p_row03_traceSegment_097_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2497 8 9, g32p_row03_traceSegment_097_2497_0008, g32p_row03_traceSegment_097_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2514 8 9, g32p_row03_traceSegment_097_2514_0008, g32p_row03_traceSegment_097_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2497 17 17, g32p_row03_traceSegment_097_2497_0017, g32p_row03_traceSegment_097_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2531 8 9, g32p_row03_traceSegment_097_2531_0008, g32p_row03_traceSegment_097_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2548 8 9, g32p_row03_traceSegment_097_2548_0008, g32p_row03_traceSegment_097_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2531 17 17, g32p_row03_traceSegment_097_2531_0017, g32p_row03_traceSegment_097_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2497 34 34, g32p_row03_traceSegment_097_2497_0034, g32p_row03_traceSegment_097_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2430 67 68, g32p_row03_traceSegment_097_2430_0067, g32p_row03_traceSegment_097_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2581 8 9, g32p_row03_traceSegment_097_2581_0008, g32p_row03_traceSegment_097_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2565 16 17, g32p_row03_traceSegment_097_2565_0016, g32p_row03_traceSegment_097_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2598 8 9, g32p_row03_traceSegment_097_2598_0008, g32p_row03_traceSegment_097_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2615 8 9, g32p_row03_traceSegment_097_2615_0008, g32p_row03_traceSegment_097_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2598 17 17, g32p_row03_traceSegment_097_2598_0017, g32p_row03_traceSegment_097_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2565 33 34, g32p_row03_traceSegment_097_2565_0033, g32p_row03_traceSegment_097_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2632 8 9, g32p_row03_traceSegment_097_2632_0008, g32p_row03_traceSegment_097_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2649 8 9, g32p_row03_traceSegment_097_2649_0008, g32p_row03_traceSegment_097_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2632 17 17, g32p_row03_traceSegment_097_2632_0017, g32p_row03_traceSegment_097_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2666 8 9, g32p_row03_traceSegment_097_2666_0008, g32p_row03_traceSegment_097_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2683 8 9, g32p_row03_traceSegment_097_2683_0008, g32p_row03_traceSegment_097_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2666 17 17, g32p_row03_traceSegment_097_2666_0017, g32p_row03_traceSegment_097_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2632 34 34, g32p_row03_traceSegment_097_2632_0034, g32p_row03_traceSegment_097_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2565 67 68, g32p_row03_traceSegment_097_2565_0067, g32p_row03_traceSegment_097_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2430 135 135, g32p_row03_traceSegment_097_2430_0135, g32p_row03_traceSegment_097_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_097 2160 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2160 270 270, g32p_row03_traceSegment_097_2160_0270, g32p_row03_traceSegment_097_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2716 8 9, g32p_row03_traceSegment_097_2716_0008, g32p_row03_traceSegment_097_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2700 16 17, g32p_row03_traceSegment_097_2700_0016, g32p_row03_traceSegment_097_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2733 8 9, g32p_row03_traceSegment_097_2733_0008, g32p_row03_traceSegment_097_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2750 8 9, g32p_row03_traceSegment_097_2750_0008, g32p_row03_traceSegment_097_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2733 17 17, g32p_row03_traceSegment_097_2733_0017, g32p_row03_traceSegment_097_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2700 33 34, g32p_row03_traceSegment_097_2700_0033, g32p_row03_traceSegment_097_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2767 8 9, g32p_row03_traceSegment_097_2767_0008, g32p_row03_traceSegment_097_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2784 8 9, g32p_row03_traceSegment_097_2784_0008, g32p_row03_traceSegment_097_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2767 17 17, g32p_row03_traceSegment_097_2767_0017, g32p_row03_traceSegment_097_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2801 8 9, g32p_row03_traceSegment_097_2801_0008, g32p_row03_traceSegment_097_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2818 8 9, g32p_row03_traceSegment_097_2818_0008, g32p_row03_traceSegment_097_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2801 17 17, g32p_row03_traceSegment_097_2801_0017, g32p_row03_traceSegment_097_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2767 34 34, g32p_row03_traceSegment_097_2767_0034, g32p_row03_traceSegment_097_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2700 67 68, g32p_row03_traceSegment_097_2700_0067, g32p_row03_traceSegment_097_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2851 8 9, g32p_row03_traceSegment_097_2851_0008, g32p_row03_traceSegment_097_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2835 16 17, g32p_row03_traceSegment_097_2835_0016, g32p_row03_traceSegment_097_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2868 8 9, g32p_row03_traceSegment_097_2868_0008, g32p_row03_traceSegment_097_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2885 8 9, g32p_row03_traceSegment_097_2885_0008, g32p_row03_traceSegment_097_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2868 17 17, g32p_row03_traceSegment_097_2868_0017, g32p_row03_traceSegment_097_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2835 33 34, g32p_row03_traceSegment_097_2835_0033, g32p_row03_traceSegment_097_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2902 8 9, g32p_row03_traceSegment_097_2902_0008, g32p_row03_traceSegment_097_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2919 8 9, g32p_row03_traceSegment_097_2919_0008, g32p_row03_traceSegment_097_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2902 17 17, g32p_row03_traceSegment_097_2902_0017, g32p_row03_traceSegment_097_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2936 8 9, g32p_row03_traceSegment_097_2936_0008, g32p_row03_traceSegment_097_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2953 8 9, g32p_row03_traceSegment_097_2953_0008, g32p_row03_traceSegment_097_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2936 17 17, g32p_row03_traceSegment_097_2936_0017, g32p_row03_traceSegment_097_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2902 34 34, g32p_row03_traceSegment_097_2902_0034, g32p_row03_traceSegment_097_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2835 67 68, g32p_row03_traceSegment_097_2835_0067, g32p_row03_traceSegment_097_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2700 135 135, g32p_row03_traceSegment_097_2700_0135, g32p_row03_traceSegment_097_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2986 8 9, g32p_row03_traceSegment_097_2986_0008, g32p_row03_traceSegment_097_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2970 16 17, g32p_row03_traceSegment_097_2970_0016, g32p_row03_traceSegment_097_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3003 8 9, g32p_row03_traceSegment_097_3003_0008, g32p_row03_traceSegment_097_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3020 8 9, g32p_row03_traceSegment_097_3020_0008, g32p_row03_traceSegment_097_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3003 17 17, g32p_row03_traceSegment_097_3003_0017, g32p_row03_traceSegment_097_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2970 33 34, g32p_row03_traceSegment_097_2970_0033, g32p_row03_traceSegment_097_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3037 8 9, g32p_row03_traceSegment_097_3037_0008, g32p_row03_traceSegment_097_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3054 8 9, g32p_row03_traceSegment_097_3054_0008, g32p_row03_traceSegment_097_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3037 17 17, g32p_row03_traceSegment_097_3037_0017, g32p_row03_traceSegment_097_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3071 8 9, g32p_row03_traceSegment_097_3071_0008, g32p_row03_traceSegment_097_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3088 8 9, g32p_row03_traceSegment_097_3088_0008, g32p_row03_traceSegment_097_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3071 17 17, g32p_row03_traceSegment_097_3071_0017, g32p_row03_traceSegment_097_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3037 34 34, g32p_row03_traceSegment_097_3037_0034, g32p_row03_traceSegment_097_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2970 67 68, g32p_row03_traceSegment_097_2970_0067, g32p_row03_traceSegment_097_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3121 8 9, g32p_row03_traceSegment_097_3121_0008, g32p_row03_traceSegment_097_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3105 16 17, g32p_row03_traceSegment_097_3105_0016, g32p_row03_traceSegment_097_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3138 8 9, g32p_row03_traceSegment_097_3138_0008, g32p_row03_traceSegment_097_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3155 8 9, g32p_row03_traceSegment_097_3155_0008, g32p_row03_traceSegment_097_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3138 17 17, g32p_row03_traceSegment_097_3138_0017, g32p_row03_traceSegment_097_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3105 33 34, g32p_row03_traceSegment_097_3105_0033, g32p_row03_traceSegment_097_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3172 8 9, g32p_row03_traceSegment_097_3172_0008, g32p_row03_traceSegment_097_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3189 8 9, g32p_row03_traceSegment_097_3189_0008, g32p_row03_traceSegment_097_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3172 17 17, g32p_row03_traceSegment_097_3172_0017, g32p_row03_traceSegment_097_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3206 8 9, g32p_row03_traceSegment_097_3206_0008, g32p_row03_traceSegment_097_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3223 8 9, g32p_row03_traceSegment_097_3223_0008, g32p_row03_traceSegment_097_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3206 17 17, g32p_row03_traceSegment_097_3206_0017, g32p_row03_traceSegment_097_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3172 34 34, g32p_row03_traceSegment_097_3172_0034, g32p_row03_traceSegment_097_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3105 67 68, g32p_row03_traceSegment_097_3105_0067, g32p_row03_traceSegment_097_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2970 135 135, g32p_row03_traceSegment_097_2970_0135, g32p_row03_traceSegment_097_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_097 2700 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2700 270 270, g32p_row03_traceSegment_097_2700_0270, g32p_row03_traceSegment_097_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_097 2160 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2160 540 540, g32p_row03_traceSegment_097_2160_0540, g32p_row03_traceSegment_097_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3256 8 9, g32p_row03_traceSegment_097_3256_0008, g32p_row03_traceSegment_097_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3240 16 17, g32p_row03_traceSegment_097_3240_0016, g32p_row03_traceSegment_097_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3273 8 9, g32p_row03_traceSegment_097_3273_0008, g32p_row03_traceSegment_097_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3290 8 9, g32p_row03_traceSegment_097_3290_0008, g32p_row03_traceSegment_097_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3273 17 17, g32p_row03_traceSegment_097_3273_0017, g32p_row03_traceSegment_097_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3240 33 34, g32p_row03_traceSegment_097_3240_0033, g32p_row03_traceSegment_097_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3307 8 9, g32p_row03_traceSegment_097_3307_0008, g32p_row03_traceSegment_097_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3324 8 9, g32p_row03_traceSegment_097_3324_0008, g32p_row03_traceSegment_097_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3307 17 17, g32p_row03_traceSegment_097_3307_0017, g32p_row03_traceSegment_097_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3341 8 9, g32p_row03_traceSegment_097_3341_0008, g32p_row03_traceSegment_097_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3358 8 9, g32p_row03_traceSegment_097_3358_0008, g32p_row03_traceSegment_097_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3341 17 17, g32p_row03_traceSegment_097_3341_0017, g32p_row03_traceSegment_097_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3307 34 34, g32p_row03_traceSegment_097_3307_0034, g32p_row03_traceSegment_097_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3240 67 68, g32p_row03_traceSegment_097_3240_0067, g32p_row03_traceSegment_097_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3391 8 9, g32p_row03_traceSegment_097_3391_0008, g32p_row03_traceSegment_097_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3375 16 17, g32p_row03_traceSegment_097_3375_0016, g32p_row03_traceSegment_097_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3408 8 9, g32p_row03_traceSegment_097_3408_0008, g32p_row03_traceSegment_097_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3425 8 9, g32p_row03_traceSegment_097_3425_0008, g32p_row03_traceSegment_097_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3408 17 17, g32p_row03_traceSegment_097_3408_0017, g32p_row03_traceSegment_097_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3375 33 34, g32p_row03_traceSegment_097_3375_0033, g32p_row03_traceSegment_097_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3442 8 9, g32p_row03_traceSegment_097_3442_0008, g32p_row03_traceSegment_097_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3459 8 9, g32p_row03_traceSegment_097_3459_0008, g32p_row03_traceSegment_097_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3442 17 17, g32p_row03_traceSegment_097_3442_0017, g32p_row03_traceSegment_097_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3476 8 9, g32p_row03_traceSegment_097_3476_0008, g32p_row03_traceSegment_097_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3493 8 9, g32p_row03_traceSegment_097_3493_0008, g32p_row03_traceSegment_097_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3476 17 17, g32p_row03_traceSegment_097_3476_0017, g32p_row03_traceSegment_097_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3442 34 34, g32p_row03_traceSegment_097_3442_0034, g32p_row03_traceSegment_097_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3375 67 68, g32p_row03_traceSegment_097_3375_0067, g32p_row03_traceSegment_097_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3240 135 135, g32p_row03_traceSegment_097_3240_0135, g32p_row03_traceSegment_097_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3526 8 9, g32p_row03_traceSegment_097_3526_0008, g32p_row03_traceSegment_097_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3510 16 17, g32p_row03_traceSegment_097_3510_0016, g32p_row03_traceSegment_097_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3543 8 9, g32p_row03_traceSegment_097_3543_0008, g32p_row03_traceSegment_097_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3560 8 9, g32p_row03_traceSegment_097_3560_0008, g32p_row03_traceSegment_097_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3543 17 17, g32p_row03_traceSegment_097_3543_0017, g32p_row03_traceSegment_097_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3510 33 34, g32p_row03_traceSegment_097_3510_0033, g32p_row03_traceSegment_097_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3577 8 9, g32p_row03_traceSegment_097_3577_0008, g32p_row03_traceSegment_097_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3594 8 9, g32p_row03_traceSegment_097_3594_0008, g32p_row03_traceSegment_097_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3577 17 17, g32p_row03_traceSegment_097_3577_0017, g32p_row03_traceSegment_097_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3611 8 9, g32p_row03_traceSegment_097_3611_0008, g32p_row03_traceSegment_097_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3628 8 9, g32p_row03_traceSegment_097_3628_0008, g32p_row03_traceSegment_097_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3611 17 17, g32p_row03_traceSegment_097_3611_0017, g32p_row03_traceSegment_097_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3577 34 34, g32p_row03_traceSegment_097_3577_0034, g32p_row03_traceSegment_097_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3510 67 68, g32p_row03_traceSegment_097_3510_0067, g32p_row03_traceSegment_097_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3661 8 9, g32p_row03_traceSegment_097_3661_0008, g32p_row03_traceSegment_097_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3645 16 17, g32p_row03_traceSegment_097_3645_0016, g32p_row03_traceSegment_097_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3678 8 9, g32p_row03_traceSegment_097_3678_0008, g32p_row03_traceSegment_097_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3695 8 9, g32p_row03_traceSegment_097_3695_0008, g32p_row03_traceSegment_097_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3678 17 17, g32p_row03_traceSegment_097_3678_0017, g32p_row03_traceSegment_097_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3645 33 34, g32p_row03_traceSegment_097_3645_0033, g32p_row03_traceSegment_097_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3712 8 9, g32p_row03_traceSegment_097_3712_0008, g32p_row03_traceSegment_097_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3729 8 9, g32p_row03_traceSegment_097_3729_0008, g32p_row03_traceSegment_097_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3712 17 17, g32p_row03_traceSegment_097_3712_0017, g32p_row03_traceSegment_097_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3746 8 9, g32p_row03_traceSegment_097_3746_0008, g32p_row03_traceSegment_097_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3763 8 9, g32p_row03_traceSegment_097_3763_0008, g32p_row03_traceSegment_097_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3746 17 17, g32p_row03_traceSegment_097_3746_0017, g32p_row03_traceSegment_097_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3712 34 34, g32p_row03_traceSegment_097_3712_0034, g32p_row03_traceSegment_097_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3645 67 68, g32p_row03_traceSegment_097_3645_0067, g32p_row03_traceSegment_097_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 3510 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3510 135 135, g32p_row03_traceSegment_097_3510_0135, g32p_row03_traceSegment_097_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_097 3240 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3240 270 270, g32p_row03_traceSegment_097_3240_0270, g32p_row03_traceSegment_097_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3796 8 9, g32p_row03_traceSegment_097_3796_0008, g32p_row03_traceSegment_097_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3780 16 17, g32p_row03_traceSegment_097_3780_0016, g32p_row03_traceSegment_097_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3813 8 9, g32p_row03_traceSegment_097_3813_0008, g32p_row03_traceSegment_097_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3830 8 9, g32p_row03_traceSegment_097_3830_0008, g32p_row03_traceSegment_097_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3813 17 17, g32p_row03_traceSegment_097_3813_0017, g32p_row03_traceSegment_097_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3780 33 34, g32p_row03_traceSegment_097_3780_0033, g32p_row03_traceSegment_097_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3847 8 9, g32p_row03_traceSegment_097_3847_0008, g32p_row03_traceSegment_097_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3864 8 9, g32p_row03_traceSegment_097_3864_0008, g32p_row03_traceSegment_097_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3847 17 17, g32p_row03_traceSegment_097_3847_0017, g32p_row03_traceSegment_097_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3881 8 9, g32p_row03_traceSegment_097_3881_0008, g32p_row03_traceSegment_097_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3898 8 9, g32p_row03_traceSegment_097_3898_0008, g32p_row03_traceSegment_097_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3881 17 17, g32p_row03_traceSegment_097_3881_0017, g32p_row03_traceSegment_097_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3847 34 34, g32p_row03_traceSegment_097_3847_0034, g32p_row03_traceSegment_097_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3780 67 68, g32p_row03_traceSegment_097_3780_0067, g32p_row03_traceSegment_097_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3931 8 9, g32p_row03_traceSegment_097_3931_0008, g32p_row03_traceSegment_097_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3915 16 17, g32p_row03_traceSegment_097_3915_0016, g32p_row03_traceSegment_097_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3948 8 9, g32p_row03_traceSegment_097_3948_0008, g32p_row03_traceSegment_097_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3965 8 9, g32p_row03_traceSegment_097_3965_0008, g32p_row03_traceSegment_097_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3948 17 17, g32p_row03_traceSegment_097_3948_0017, g32p_row03_traceSegment_097_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3915 33 34, g32p_row03_traceSegment_097_3915_0033, g32p_row03_traceSegment_097_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3982 8 9, g32p_row03_traceSegment_097_3982_0008, g32p_row03_traceSegment_097_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3999 8 9, g32p_row03_traceSegment_097_3999_0008, g32p_row03_traceSegment_097_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3982 17 17, g32p_row03_traceSegment_097_3982_0017, g32p_row03_traceSegment_097_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4016 8 9, g32p_row03_traceSegment_097_4016_0008, g32p_row03_traceSegment_097_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4033 8 9, g32p_row03_traceSegment_097_4033_0008, g32p_row03_traceSegment_097_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4016 17 17, g32p_row03_traceSegment_097_4016_0017, g32p_row03_traceSegment_097_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3982 34 34, g32p_row03_traceSegment_097_3982_0034, g32p_row03_traceSegment_097_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3915 67 68, g32p_row03_traceSegment_097_3915_0067, g32p_row03_traceSegment_097_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3780 135 135, g32p_row03_traceSegment_097_3780_0135, g32p_row03_traceSegment_097_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4066 8 9, g32p_row03_traceSegment_097_4066_0008, g32p_row03_traceSegment_097_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4050 16 17, g32p_row03_traceSegment_097_4050_0016, g32p_row03_traceSegment_097_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4083 8 9, g32p_row03_traceSegment_097_4083_0008, g32p_row03_traceSegment_097_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4100 8 9, g32p_row03_traceSegment_097_4100_0008, g32p_row03_traceSegment_097_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4083 17 17, g32p_row03_traceSegment_097_4083_0017, g32p_row03_traceSegment_097_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4050 33 34, g32p_row03_traceSegment_097_4050_0033, g32p_row03_traceSegment_097_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4117 8 9, g32p_row03_traceSegment_097_4117_0008, g32p_row03_traceSegment_097_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4134 8 9, g32p_row03_traceSegment_097_4134_0008, g32p_row03_traceSegment_097_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4117 17 17, g32p_row03_traceSegment_097_4117_0017, g32p_row03_traceSegment_097_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4151 8 9, g32p_row03_traceSegment_097_4151_0008, g32p_row03_traceSegment_097_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4168 8 9, g32p_row03_traceSegment_097_4168_0008, g32p_row03_traceSegment_097_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4151 17 17, g32p_row03_traceSegment_097_4151_0017, g32p_row03_traceSegment_097_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4117 34 34, g32p_row03_traceSegment_097_4117_0034, g32p_row03_traceSegment_097_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4050 67 68, g32p_row03_traceSegment_097_4050_0067, g32p_row03_traceSegment_097_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_097 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4201 8 9, g32p_row03_traceSegment_097_4201_0008, g32p_row03_traceSegment_097_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_097 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4185 16 17, g32p_row03_traceSegment_097_4185_0016, g32p_row03_traceSegment_097_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4218 8 9, g32p_row03_traceSegment_097_4218_0008, g32p_row03_traceSegment_097_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4235 8 9, g32p_row03_traceSegment_097_4235_0008, g32p_row03_traceSegment_097_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4218 17 17, g32p_row03_traceSegment_097_4218_0017, g32p_row03_traceSegment_097_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_097 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4185 33 34, g32p_row03_traceSegment_097_4185_0033, g32p_row03_traceSegment_097_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4252 8 9, g32p_row03_traceSegment_097_4252_0008, g32p_row03_traceSegment_097_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4269 8 9, g32p_row03_traceSegment_097_4269_0008, g32p_row03_traceSegment_097_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4252 17 17, g32p_row03_traceSegment_097_4252_0017, g32p_row03_traceSegment_097_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4286 8 9, g32p_row03_traceSegment_097_4286_0008, g32p_row03_traceSegment_097_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_097 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_097 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_097_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_097 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4303 8 9, g32p_row03_traceSegment_097_4303_0008, g32p_row03_traceSegment_097_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_097 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4286 17 17, g32p_row03_traceSegment_097_4286_0017, g32p_row03_traceSegment_097_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_097 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4252 34 34, g32p_row03_traceSegment_097_4252_0034, g32p_row03_traceSegment_097_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_097 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4185 67 68, g32p_row03_traceSegment_097_4185_0067, g32p_row03_traceSegment_097_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_097_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_097 4050 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 4050 135 135, g32p_row03_traceSegment_097_4050_0135, g32p_row03_traceSegment_097_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_097 3780 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3780 270 270, g32p_row03_traceSegment_097_3780_0270, g32p_row03_traceSegment_097_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_097_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_097 3240 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 3240 540 540, g32p_row03_traceSegment_097_3240_0540, g32p_row03_traceSegment_097_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_097_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_097 2160 2160 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 2160 1080 1080, g32p_row03_traceSegment_097_2160_1080, g32p_row03_traceSegment_097_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_097_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_097 0 4320 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_097 0 2160 2160, g32p_row03_traceSegment_097_0000_2160, g32p_row03_traceSegment_097_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 97 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_097_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 75) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 75) (g32p_literalTraceValue 2 75)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_075]
  decide +kernel

theorem g32p_row03_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 78) (g32p_literalTraceValue 2 78)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_078]
  decide +kernel

theorem g32p_row03_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 82) (g32p_literalTraceValue 2 82)
      [1, -1, 1] [0, 0, 51840, 51840] = true := by
  rw [g32p_row03_traceCoefficients_082]
  decide +kernel

theorem g32p_row03_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 84) (g32p_literalTraceValue 2 84)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_084]
  decide +kernel

theorem g32p_row03_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 86) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 86) (g32p_literalTraceValue 2 86)
      [1, -1, 1] [0, 0, 12960, 12960] = true := by
  rw [g32p_row03_traceCoefficients_086]
  decide +kernel

theorem g32p_row03_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 92) (g32p_literalTraceValue 2 92)
      [1, -1, 1] [25920, 25920, 25920] = true := by
  rw [g32p_row03_traceCoefficients_092]
  decide +kernel

theorem g32p_row03_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 96) (g32p_literalTraceValue 2 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_096]
  decide +kernel

theorem g32p_row03_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 97) (g32p_literalTraceValue 2 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_097]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
