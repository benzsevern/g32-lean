import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_006 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 6 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_006_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 16 8 9, g32p_row03_traceSegment_006_0016_0008, g32p_row03_traceSegment_006_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 0 16 17, g32p_row03_traceSegment_006_0000_0016, g32p_row03_traceSegment_006_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 33 8 9, g32p_row03_traceSegment_006_0033_0008, g32p_row03_traceSegment_006_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 50 8 9, g32p_row03_traceSegment_006_0050_0008, g32p_row03_traceSegment_006_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 33 17 17, g32p_row03_traceSegment_006_0033_0017, g32p_row03_traceSegment_006_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 0 33 34, g32p_row03_traceSegment_006_0000_0033, g32p_row03_traceSegment_006_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 67 8 9, g32p_row03_traceSegment_006_0067_0008, g32p_row03_traceSegment_006_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 84 8 9, g32p_row03_traceSegment_006_0084_0008, g32p_row03_traceSegment_006_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 67 17 17, g32p_row03_traceSegment_006_0067_0017, g32p_row03_traceSegment_006_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 101 8 9, g32p_row03_traceSegment_006_0101_0008, g32p_row03_traceSegment_006_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 118 8 9, g32p_row03_traceSegment_006_0118_0008, g32p_row03_traceSegment_006_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 101 17 17, g32p_row03_traceSegment_006_0101_0017, g32p_row03_traceSegment_006_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 67 34 34, g32p_row03_traceSegment_006_0067_0034, g32p_row03_traceSegment_006_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 0 67 68, g32p_row03_traceSegment_006_0000_0067, g32p_row03_traceSegment_006_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 151 8 9, g32p_row03_traceSegment_006_0151_0008, g32p_row03_traceSegment_006_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 135 16 17, g32p_row03_traceSegment_006_0135_0016, g32p_row03_traceSegment_006_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 168 8 9, g32p_row03_traceSegment_006_0168_0008, g32p_row03_traceSegment_006_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 185 8 9, g32p_row03_traceSegment_006_0185_0008, g32p_row03_traceSegment_006_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 168 17 17, g32p_row03_traceSegment_006_0168_0017, g32p_row03_traceSegment_006_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 135 33 34, g32p_row03_traceSegment_006_0135_0033, g32p_row03_traceSegment_006_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 202 8 9, g32p_row03_traceSegment_006_0202_0008, g32p_row03_traceSegment_006_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 219 8 9, g32p_row03_traceSegment_006_0219_0008, g32p_row03_traceSegment_006_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 202 17 17, g32p_row03_traceSegment_006_0202_0017, g32p_row03_traceSegment_006_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 236 8 9, g32p_row03_traceSegment_006_0236_0008, g32p_row03_traceSegment_006_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 253 8 9, g32p_row03_traceSegment_006_0253_0008, g32p_row03_traceSegment_006_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 236 17 17, g32p_row03_traceSegment_006_0236_0017, g32p_row03_traceSegment_006_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 202 34 34, g32p_row03_traceSegment_006_0202_0034, g32p_row03_traceSegment_006_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 135 67 68, g32p_row03_traceSegment_006_0135_0067, g32p_row03_traceSegment_006_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 0 135 135, g32p_row03_traceSegment_006_0000_0135, g32p_row03_traceSegment_006_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 286 8 9, g32p_row03_traceSegment_006_0286_0008, g32p_row03_traceSegment_006_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 270 16 17, g32p_row03_traceSegment_006_0270_0016, g32p_row03_traceSegment_006_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 311 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 303 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 303 8 9, g32p_row03_traceSegment_006_0303_0008, g32p_row03_traceSegment_006_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 320 8 9, g32p_row03_traceSegment_006_0320_0008, g32p_row03_traceSegment_006_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 303 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 303 17 17, g32p_row03_traceSegment_006_0303_0017, g32p_row03_traceSegment_006_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 270 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 270 33 34, g32p_row03_traceSegment_006_0270_0033, g32p_row03_traceSegment_006_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 337 8 9, g32p_row03_traceSegment_006_0337_0008, g32p_row03_traceSegment_006_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 354 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 354 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 354 8 9, g32p_row03_traceSegment_006_0354_0008, g32p_row03_traceSegment_006_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 337 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 337 17 17, g32p_row03_traceSegment_006_0337_0017, g32p_row03_traceSegment_006_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 379 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 371 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 371 8 9, g32p_row03_traceSegment_006_0371_0008, g32p_row03_traceSegment_006_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 396 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 388 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 388 8 9, g32p_row03_traceSegment_006_0388_0008, g32p_row03_traceSegment_006_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 371 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 371 17 17, g32p_row03_traceSegment_006_0371_0017, g32p_row03_traceSegment_006_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 337 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 337 34 34, g32p_row03_traceSegment_006_0337_0034, g32p_row03_traceSegment_006_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 270 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 270 67 68, g32p_row03_traceSegment_006_0270_0067, g32p_row03_traceSegment_006_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 421 8 9, g32p_row03_traceSegment_006_0421_0008, g32p_row03_traceSegment_006_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 405 16 17, g32p_row03_traceSegment_006_0405_0016, g32p_row03_traceSegment_006_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 438 8 9, g32p_row03_traceSegment_006_0438_0008, g32p_row03_traceSegment_006_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 455 8 9, g32p_row03_traceSegment_006_0455_0008, g32p_row03_traceSegment_006_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 438 17 17, g32p_row03_traceSegment_006_0438_0017, g32p_row03_traceSegment_006_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 405 33 34, g32p_row03_traceSegment_006_0405_0033, g32p_row03_traceSegment_006_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 472 8 9, g32p_row03_traceSegment_006_0472_0008, g32p_row03_traceSegment_006_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 489 8 9, g32p_row03_traceSegment_006_0489_0008, g32p_row03_traceSegment_006_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 472 17 17, g32p_row03_traceSegment_006_0472_0017, g32p_row03_traceSegment_006_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 506 8 9, g32p_row03_traceSegment_006_0506_0008, g32p_row03_traceSegment_006_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 523 8 9, g32p_row03_traceSegment_006_0523_0008, g32p_row03_traceSegment_006_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 506 17 17, g32p_row03_traceSegment_006_0506_0017, g32p_row03_traceSegment_006_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 472 34 34, g32p_row03_traceSegment_006_0472_0034, g32p_row03_traceSegment_006_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 405 67 68, g32p_row03_traceSegment_006_0405_0067, g32p_row03_traceSegment_006_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 270 270 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 270 135 135, g32p_row03_traceSegment_006_0270_0135, g32p_row03_traceSegment_006_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_006 0 540 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 0 270 270, g32p_row03_traceSegment_006_0000_0270, g32p_row03_traceSegment_006_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 556 8 9, g32p_row03_traceSegment_006_0556_0008, g32p_row03_traceSegment_006_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 540 16 17, g32p_row03_traceSegment_006_0540_0016, g32p_row03_traceSegment_006_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 573 8 9, g32p_row03_traceSegment_006_0573_0008, g32p_row03_traceSegment_006_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 590 8 9, g32p_row03_traceSegment_006_0590_0008, g32p_row03_traceSegment_006_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 573 17 17, g32p_row03_traceSegment_006_0573_0017, g32p_row03_traceSegment_006_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 540 33 34, g32p_row03_traceSegment_006_0540_0033, g32p_row03_traceSegment_006_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 607 8 9, g32p_row03_traceSegment_006_0607_0008, g32p_row03_traceSegment_006_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 624 8 9, g32p_row03_traceSegment_006_0624_0008, g32p_row03_traceSegment_006_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 607 17 17, g32p_row03_traceSegment_006_0607_0017, g32p_row03_traceSegment_006_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 641 8 9, g32p_row03_traceSegment_006_0641_0008, g32p_row03_traceSegment_006_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 658 8 9, g32p_row03_traceSegment_006_0658_0008, g32p_row03_traceSegment_006_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 641 17 17, g32p_row03_traceSegment_006_0641_0017, g32p_row03_traceSegment_006_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 607 34 34, g32p_row03_traceSegment_006_0607_0034, g32p_row03_traceSegment_006_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 540 67 68, g32p_row03_traceSegment_006_0540_0067, g32p_row03_traceSegment_006_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 691 8 9, g32p_row03_traceSegment_006_0691_0008, g32p_row03_traceSegment_006_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 675 16 17, g32p_row03_traceSegment_006_0675_0016, g32p_row03_traceSegment_006_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 708 8 9, g32p_row03_traceSegment_006_0708_0008, g32p_row03_traceSegment_006_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 725 8 9, g32p_row03_traceSegment_006_0725_0008, g32p_row03_traceSegment_006_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 708 17 17, g32p_row03_traceSegment_006_0708_0017, g32p_row03_traceSegment_006_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 675 33 34, g32p_row03_traceSegment_006_0675_0033, g32p_row03_traceSegment_006_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 742 8 9, g32p_row03_traceSegment_006_0742_0008, g32p_row03_traceSegment_006_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 759 8 9, g32p_row03_traceSegment_006_0759_0008, g32p_row03_traceSegment_006_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 742 17 17, g32p_row03_traceSegment_006_0742_0017, g32p_row03_traceSegment_006_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 776 8 9, g32p_row03_traceSegment_006_0776_0008, g32p_row03_traceSegment_006_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 793 8 9, g32p_row03_traceSegment_006_0793_0008, g32p_row03_traceSegment_006_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 776 17 17, g32p_row03_traceSegment_006_0776_0017, g32p_row03_traceSegment_006_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 742 34 34, g32p_row03_traceSegment_006_0742_0034, g32p_row03_traceSegment_006_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 675 67 68, g32p_row03_traceSegment_006_0675_0067, g32p_row03_traceSegment_006_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 540 135 135, g32p_row03_traceSegment_006_0540_0135, g32p_row03_traceSegment_006_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 826 8 9, g32p_row03_traceSegment_006_0826_0008, g32p_row03_traceSegment_006_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 810 16 17, g32p_row03_traceSegment_006_0810_0016, g32p_row03_traceSegment_006_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 843 8 9, g32p_row03_traceSegment_006_0843_0008, g32p_row03_traceSegment_006_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 860 8 9, g32p_row03_traceSegment_006_0860_0008, g32p_row03_traceSegment_006_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 843 17 17, g32p_row03_traceSegment_006_0843_0017, g32p_row03_traceSegment_006_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 810 33 34, g32p_row03_traceSegment_006_0810_0033, g32p_row03_traceSegment_006_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 877 8 9, g32p_row03_traceSegment_006_0877_0008, g32p_row03_traceSegment_006_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 894 8 9, g32p_row03_traceSegment_006_0894_0008, g32p_row03_traceSegment_006_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 877 17 17, g32p_row03_traceSegment_006_0877_0017, g32p_row03_traceSegment_006_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 911 8 9, g32p_row03_traceSegment_006_0911_0008, g32p_row03_traceSegment_006_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 928 8 9, g32p_row03_traceSegment_006_0928_0008, g32p_row03_traceSegment_006_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 911 17 17, g32p_row03_traceSegment_006_0911_0017, g32p_row03_traceSegment_006_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 877 34 34, g32p_row03_traceSegment_006_0877_0034, g32p_row03_traceSegment_006_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 810 67 68, g32p_row03_traceSegment_006_0810_0067, g32p_row03_traceSegment_006_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 961 8 9, g32p_row03_traceSegment_006_0961_0008, g32p_row03_traceSegment_006_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 945 16 17, g32p_row03_traceSegment_006_0945_0016, g32p_row03_traceSegment_006_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 978 8 9, g32p_row03_traceSegment_006_0978_0008, g32p_row03_traceSegment_006_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 995 8 9, g32p_row03_traceSegment_006_0995_0008, g32p_row03_traceSegment_006_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 978 17 17, g32p_row03_traceSegment_006_0978_0017, g32p_row03_traceSegment_006_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 945 33 34, g32p_row03_traceSegment_006_0945_0033, g32p_row03_traceSegment_006_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1012 8 9, g32p_row03_traceSegment_006_1012_0008, g32p_row03_traceSegment_006_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1029 8 9, g32p_row03_traceSegment_006_1029_0008, g32p_row03_traceSegment_006_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1012 17 17, g32p_row03_traceSegment_006_1012_0017, g32p_row03_traceSegment_006_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1046 8 9, g32p_row03_traceSegment_006_1046_0008, g32p_row03_traceSegment_006_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1063 8 9, g32p_row03_traceSegment_006_1063_0008, g32p_row03_traceSegment_006_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1046 17 17, g32p_row03_traceSegment_006_1046_0017, g32p_row03_traceSegment_006_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1012 34 34, g32p_row03_traceSegment_006_1012_0034, g32p_row03_traceSegment_006_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 945 67 68, g32p_row03_traceSegment_006_0945_0067, g32p_row03_traceSegment_006_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 810 135 135, g32p_row03_traceSegment_006_0810_0135, g32p_row03_traceSegment_006_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_006 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 540 270 270, g32p_row03_traceSegment_006_0540_0270, g32p_row03_traceSegment_006_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_006 0 1080 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 0 540 540, g32p_row03_traceSegment_006_0000_0540, g32p_row03_traceSegment_006_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1096 8 9, g32p_row03_traceSegment_006_1096_0008, g32p_row03_traceSegment_006_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1080 16 17, g32p_row03_traceSegment_006_1080_0016, g32p_row03_traceSegment_006_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1113 8 9, g32p_row03_traceSegment_006_1113_0008, g32p_row03_traceSegment_006_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1130 8 9, g32p_row03_traceSegment_006_1130_0008, g32p_row03_traceSegment_006_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1113 17 17, g32p_row03_traceSegment_006_1113_0017, g32p_row03_traceSegment_006_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1080 33 34, g32p_row03_traceSegment_006_1080_0033, g32p_row03_traceSegment_006_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1147 8 9, g32p_row03_traceSegment_006_1147_0008, g32p_row03_traceSegment_006_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1164 8 9, g32p_row03_traceSegment_006_1164_0008, g32p_row03_traceSegment_006_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1147 17 17, g32p_row03_traceSegment_006_1147_0017, g32p_row03_traceSegment_006_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1181 8 9, g32p_row03_traceSegment_006_1181_0008, g32p_row03_traceSegment_006_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1198 8 9, g32p_row03_traceSegment_006_1198_0008, g32p_row03_traceSegment_006_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1181 17 17, g32p_row03_traceSegment_006_1181_0017, g32p_row03_traceSegment_006_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1147 34 34, g32p_row03_traceSegment_006_1147_0034, g32p_row03_traceSegment_006_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1080 67 68, g32p_row03_traceSegment_006_1080_0067, g32p_row03_traceSegment_006_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1231 8 9, g32p_row03_traceSegment_006_1231_0008, g32p_row03_traceSegment_006_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1215 16 17, g32p_row03_traceSegment_006_1215_0016, g32p_row03_traceSegment_006_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1248 8 9, g32p_row03_traceSegment_006_1248_0008, g32p_row03_traceSegment_006_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1265 8 9, g32p_row03_traceSegment_006_1265_0008, g32p_row03_traceSegment_006_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1248 17 17, g32p_row03_traceSegment_006_1248_0017, g32p_row03_traceSegment_006_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1215 33 34, g32p_row03_traceSegment_006_1215_0033, g32p_row03_traceSegment_006_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1282 8 9, g32p_row03_traceSegment_006_1282_0008, g32p_row03_traceSegment_006_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1299 8 9, g32p_row03_traceSegment_006_1299_0008, g32p_row03_traceSegment_006_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1282 17 17, g32p_row03_traceSegment_006_1282_0017, g32p_row03_traceSegment_006_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1316 8 9, g32p_row03_traceSegment_006_1316_0008, g32p_row03_traceSegment_006_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1333 8 9, g32p_row03_traceSegment_006_1333_0008, g32p_row03_traceSegment_006_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1316 17 17, g32p_row03_traceSegment_006_1316_0017, g32p_row03_traceSegment_006_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1282 34 34, g32p_row03_traceSegment_006_1282_0034, g32p_row03_traceSegment_006_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1215 67 68, g32p_row03_traceSegment_006_1215_0067, g32p_row03_traceSegment_006_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1080 135 135, g32p_row03_traceSegment_006_1080_0135, g32p_row03_traceSegment_006_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1366 8 9, g32p_row03_traceSegment_006_1366_0008, g32p_row03_traceSegment_006_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1350 16 17, g32p_row03_traceSegment_006_1350_0016, g32p_row03_traceSegment_006_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1383 8 9, g32p_row03_traceSegment_006_1383_0008, g32p_row03_traceSegment_006_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1400 8 9, g32p_row03_traceSegment_006_1400_0008, g32p_row03_traceSegment_006_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1383 17 17, g32p_row03_traceSegment_006_1383_0017, g32p_row03_traceSegment_006_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1350 33 34, g32p_row03_traceSegment_006_1350_0033, g32p_row03_traceSegment_006_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1417 8 9, g32p_row03_traceSegment_006_1417_0008, g32p_row03_traceSegment_006_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1434 8 9, g32p_row03_traceSegment_006_1434_0008, g32p_row03_traceSegment_006_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1417 17 17, g32p_row03_traceSegment_006_1417_0017, g32p_row03_traceSegment_006_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1451 8 9, g32p_row03_traceSegment_006_1451_0008, g32p_row03_traceSegment_006_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1468 8 9, g32p_row03_traceSegment_006_1468_0008, g32p_row03_traceSegment_006_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1451 17 17, g32p_row03_traceSegment_006_1451_0017, g32p_row03_traceSegment_006_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1417 34 34, g32p_row03_traceSegment_006_1417_0034, g32p_row03_traceSegment_006_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1350 67 68, g32p_row03_traceSegment_006_1350_0067, g32p_row03_traceSegment_006_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1501 8 9, g32p_row03_traceSegment_006_1501_0008, g32p_row03_traceSegment_006_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1485 16 17, g32p_row03_traceSegment_006_1485_0016, g32p_row03_traceSegment_006_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1518 8 9, g32p_row03_traceSegment_006_1518_0008, g32p_row03_traceSegment_006_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1535 8 9, g32p_row03_traceSegment_006_1535_0008, g32p_row03_traceSegment_006_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1518 17 17, g32p_row03_traceSegment_006_1518_0017, g32p_row03_traceSegment_006_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1485 33 34, g32p_row03_traceSegment_006_1485_0033, g32p_row03_traceSegment_006_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1552 8 9, g32p_row03_traceSegment_006_1552_0008, g32p_row03_traceSegment_006_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1569 8 9, g32p_row03_traceSegment_006_1569_0008, g32p_row03_traceSegment_006_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1552 17 17, g32p_row03_traceSegment_006_1552_0017, g32p_row03_traceSegment_006_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1586 8 9, g32p_row03_traceSegment_006_1586_0008, g32p_row03_traceSegment_006_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1603 8 9, g32p_row03_traceSegment_006_1603_0008, g32p_row03_traceSegment_006_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1586 17 17, g32p_row03_traceSegment_006_1586_0017, g32p_row03_traceSegment_006_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1552 34 34, g32p_row03_traceSegment_006_1552_0034, g32p_row03_traceSegment_006_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1485 67 68, g32p_row03_traceSegment_006_1485_0067, g32p_row03_traceSegment_006_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1350 135 135, g32p_row03_traceSegment_006_1350_0135, g32p_row03_traceSegment_006_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_006 1080 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1080 270 270, g32p_row03_traceSegment_006_1080_0270, g32p_row03_traceSegment_006_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1636 8 9, g32p_row03_traceSegment_006_1636_0008, g32p_row03_traceSegment_006_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1620 16 17, g32p_row03_traceSegment_006_1620_0016, g32p_row03_traceSegment_006_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1653 8 9, g32p_row03_traceSegment_006_1653_0008, g32p_row03_traceSegment_006_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1670 8 9, g32p_row03_traceSegment_006_1670_0008, g32p_row03_traceSegment_006_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1653 17 17, g32p_row03_traceSegment_006_1653_0017, g32p_row03_traceSegment_006_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1620 33 34, g32p_row03_traceSegment_006_1620_0033, g32p_row03_traceSegment_006_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1687 8 9, g32p_row03_traceSegment_006_1687_0008, g32p_row03_traceSegment_006_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1704 8 9, g32p_row03_traceSegment_006_1704_0008, g32p_row03_traceSegment_006_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1687 17 17, g32p_row03_traceSegment_006_1687_0017, g32p_row03_traceSegment_006_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1721 8 9, g32p_row03_traceSegment_006_1721_0008, g32p_row03_traceSegment_006_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1738 8 9, g32p_row03_traceSegment_006_1738_0008, g32p_row03_traceSegment_006_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1721 17 17, g32p_row03_traceSegment_006_1721_0017, g32p_row03_traceSegment_006_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1687 34 34, g32p_row03_traceSegment_006_1687_0034, g32p_row03_traceSegment_006_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1620 67 68, g32p_row03_traceSegment_006_1620_0067, g32p_row03_traceSegment_006_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1771 8 9, g32p_row03_traceSegment_006_1771_0008, g32p_row03_traceSegment_006_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1755 16 17, g32p_row03_traceSegment_006_1755_0016, g32p_row03_traceSegment_006_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1788 8 9, g32p_row03_traceSegment_006_1788_0008, g32p_row03_traceSegment_006_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1805 8 9, g32p_row03_traceSegment_006_1805_0008, g32p_row03_traceSegment_006_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1788 17 17, g32p_row03_traceSegment_006_1788_0017, g32p_row03_traceSegment_006_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1755 33 34, g32p_row03_traceSegment_006_1755_0033, g32p_row03_traceSegment_006_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1822 8 9, g32p_row03_traceSegment_006_1822_0008, g32p_row03_traceSegment_006_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1839 8 9, g32p_row03_traceSegment_006_1839_0008, g32p_row03_traceSegment_006_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1822 17 17, g32p_row03_traceSegment_006_1822_0017, g32p_row03_traceSegment_006_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1856 8 9, g32p_row03_traceSegment_006_1856_0008, g32p_row03_traceSegment_006_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1873 8 9, g32p_row03_traceSegment_006_1873_0008, g32p_row03_traceSegment_006_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1856 17 17, g32p_row03_traceSegment_006_1856_0017, g32p_row03_traceSegment_006_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1822 34 34, g32p_row03_traceSegment_006_1822_0034, g32p_row03_traceSegment_006_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1755 67 68, g32p_row03_traceSegment_006_1755_0067, g32p_row03_traceSegment_006_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1620 135 135, g32p_row03_traceSegment_006_1620_0135, g32p_row03_traceSegment_006_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1906 8 9, g32p_row03_traceSegment_006_1906_0008, g32p_row03_traceSegment_006_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1890 16 17, g32p_row03_traceSegment_006_1890_0016, g32p_row03_traceSegment_006_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1923 8 9, g32p_row03_traceSegment_006_1923_0008, g32p_row03_traceSegment_006_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1940 8 9, g32p_row03_traceSegment_006_1940_0008, g32p_row03_traceSegment_006_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1923 17 17, g32p_row03_traceSegment_006_1923_0017, g32p_row03_traceSegment_006_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1890 33 34, g32p_row03_traceSegment_006_1890_0033, g32p_row03_traceSegment_006_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1957 8 9, g32p_row03_traceSegment_006_1957_0008, g32p_row03_traceSegment_006_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1974 8 9, g32p_row03_traceSegment_006_1974_0008, g32p_row03_traceSegment_006_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1957 17 17, g32p_row03_traceSegment_006_1957_0017, g32p_row03_traceSegment_006_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1991 8 9, g32p_row03_traceSegment_006_1991_0008, g32p_row03_traceSegment_006_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2008 8 9, g32p_row03_traceSegment_006_2008_0008, g32p_row03_traceSegment_006_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1991 17 17, g32p_row03_traceSegment_006_1991_0017, g32p_row03_traceSegment_006_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1957 34 34, g32p_row03_traceSegment_006_1957_0034, g32p_row03_traceSegment_006_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1890 67 68, g32p_row03_traceSegment_006_1890_0067, g32p_row03_traceSegment_006_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2041 8 9, g32p_row03_traceSegment_006_2041_0008, g32p_row03_traceSegment_006_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2025 16 17, g32p_row03_traceSegment_006_2025_0016, g32p_row03_traceSegment_006_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2058 8 9, g32p_row03_traceSegment_006_2058_0008, g32p_row03_traceSegment_006_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2075 8 9, g32p_row03_traceSegment_006_2075_0008, g32p_row03_traceSegment_006_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2058 17 17, g32p_row03_traceSegment_006_2058_0017, g32p_row03_traceSegment_006_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2025 33 34, g32p_row03_traceSegment_006_2025_0033, g32p_row03_traceSegment_006_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2092 8 9, g32p_row03_traceSegment_006_2092_0008, g32p_row03_traceSegment_006_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2109 8 9, g32p_row03_traceSegment_006_2109_0008, g32p_row03_traceSegment_006_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2092 17 17, g32p_row03_traceSegment_006_2092_0017, g32p_row03_traceSegment_006_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2126 8 9, g32p_row03_traceSegment_006_2126_0008, g32p_row03_traceSegment_006_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2151 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2143 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2143 8 9, g32p_row03_traceSegment_006_2143_0008, g32p_row03_traceSegment_006_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2126 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2126 17 17, g32p_row03_traceSegment_006_2126_0017, g32p_row03_traceSegment_006_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 2092 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2092 34 34, g32p_row03_traceSegment_006_2092_0034, g32p_row03_traceSegment_006_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 2025 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2025 67 68, g32p_row03_traceSegment_006_2025_0067, g32p_row03_traceSegment_006_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 1890 270 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1890 135 135, g32p_row03_traceSegment_006_1890_0135, g32p_row03_traceSegment_006_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_006 1620 540 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1620 270 270, g32p_row03_traceSegment_006_1620_0270, g32p_row03_traceSegment_006_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_006_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_006 1080 1080 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 1080 540 540, g32p_row03_traceSegment_006_1080_0540, g32p_row03_traceSegment_006_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_006 0 2160 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 0 1080 1080, g32p_row03_traceSegment_006_0000_1080, g32p_row03_traceSegment_006_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2176 8 9, g32p_row03_traceSegment_006_2176_0008, g32p_row03_traceSegment_006_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2160 16 17, g32p_row03_traceSegment_006_2160_0016, g32p_row03_traceSegment_006_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2201 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2193 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2193 8 9, g32p_row03_traceSegment_006_2193_0008, g32p_row03_traceSegment_006_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2210 8 9, g32p_row03_traceSegment_006_2210_0008, g32p_row03_traceSegment_006_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2193 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2193 17 17, g32p_row03_traceSegment_006_2193_0017, g32p_row03_traceSegment_006_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 2160 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2160 33 34, g32p_row03_traceSegment_006_2160_0033, g32p_row03_traceSegment_006_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2227 8 9, g32p_row03_traceSegment_006_2227_0008, g32p_row03_traceSegment_006_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2244 8 9, g32p_row03_traceSegment_006_2244_0008, g32p_row03_traceSegment_006_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2227 17 17, g32p_row03_traceSegment_006_2227_0017, g32p_row03_traceSegment_006_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2261 8 9, g32p_row03_traceSegment_006_2261_0008, g32p_row03_traceSegment_006_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2278 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2286 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2278 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2278 8 9, g32p_row03_traceSegment_006_2278_0008, g32p_row03_traceSegment_006_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2261 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2261 17 17, g32p_row03_traceSegment_006_2261_0017, g32p_row03_traceSegment_006_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 2227 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2227 34 34, g32p_row03_traceSegment_006_2227_0034, g32p_row03_traceSegment_006_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 2160 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2160 67 68, g32p_row03_traceSegment_006_2160_0067, g32p_row03_traceSegment_006_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 2295 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2311 8 9, g32p_row03_traceSegment_006_2311_0008, g32p_row03_traceSegment_006_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 2295 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2295 16 17, g32p_row03_traceSegment_006_2295_0016, g32p_row03_traceSegment_006_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2328 8 9, g32p_row03_traceSegment_006_2328_0008, g32p_row03_traceSegment_006_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2345 8 9, g32p_row03_traceSegment_006_2345_0008, g32p_row03_traceSegment_006_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2328 17 17, g32p_row03_traceSegment_006_2328_0017, g32p_row03_traceSegment_006_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 2295 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2295 33 34, g32p_row03_traceSegment_006_2295_0033, g32p_row03_traceSegment_006_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2362 8 9, g32p_row03_traceSegment_006_2362_0008, g32p_row03_traceSegment_006_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2379 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2387 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2379 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2379 8 9, g32p_row03_traceSegment_006_2379_0008, g32p_row03_traceSegment_006_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2362 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2362 17 17, g32p_row03_traceSegment_006_2362_0017, g32p_row03_traceSegment_006_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2396 8 9, g32p_row03_traceSegment_006_2396_0008, g32p_row03_traceSegment_006_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2413 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2421 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2413 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2413 8 9, g32p_row03_traceSegment_006_2413_0008, g32p_row03_traceSegment_006_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2396 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2396 17 17, g32p_row03_traceSegment_006_2396_0017, g32p_row03_traceSegment_006_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 2362 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2362 34 34, g32p_row03_traceSegment_006_2362_0034, g32p_row03_traceSegment_006_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 2295 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2295 67 68, g32p_row03_traceSegment_006_2295_0067, g32p_row03_traceSegment_006_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 2160 270 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2160 135 135, g32p_row03_traceSegment_006_2160_0135, g32p_row03_traceSegment_006_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 2430 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2446 8 9, g32p_row03_traceSegment_006_2446_0008, g32p_row03_traceSegment_006_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 2430 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2430 16 17, g32p_row03_traceSegment_006_2430_0016, g32p_row03_traceSegment_006_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2471 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2463 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2463 8 9, g32p_row03_traceSegment_006_2463_0008, g32p_row03_traceSegment_006_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2480 8 9, g32p_row03_traceSegment_006_2480_0008, g32p_row03_traceSegment_006_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2463 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2463 17 17, g32p_row03_traceSegment_006_2463_0017, g32p_row03_traceSegment_006_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 2430 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2430 33 34, g32p_row03_traceSegment_006_2430_0033, g32p_row03_traceSegment_006_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2505 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2497 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2497 8 9, g32p_row03_traceSegment_006_2497_0008, g32p_row03_traceSegment_006_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2514 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2514 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2514 8 9, g32p_row03_traceSegment_006_2514_0008, g32p_row03_traceSegment_006_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2497 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2497 17 17, g32p_row03_traceSegment_006_2497_0017, g32p_row03_traceSegment_006_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2531 8 9, g32p_row03_traceSegment_006_2531_0008, g32p_row03_traceSegment_006_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2548 8 9, g32p_row03_traceSegment_006_2548_0008, g32p_row03_traceSegment_006_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2531 17 17, g32p_row03_traceSegment_006_2531_0017, g32p_row03_traceSegment_006_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 2497 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2497 34 34, g32p_row03_traceSegment_006_2497_0034, g32p_row03_traceSegment_006_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 2430 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2430 67 68, g32p_row03_traceSegment_006_2430_0067, g32p_row03_traceSegment_006_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2581 8 9, g32p_row03_traceSegment_006_2581_0008, g32p_row03_traceSegment_006_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2565 16 17, g32p_row03_traceSegment_006_2565_0016, g32p_row03_traceSegment_006_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2598 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2598 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2598 8 9, g32p_row03_traceSegment_006_2598_0008, g32p_row03_traceSegment_006_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2615 8 9, g32p_row03_traceSegment_006_2615_0008, g32p_row03_traceSegment_006_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2598 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2598 17 17, g32p_row03_traceSegment_006_2598_0017, g32p_row03_traceSegment_006_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 2565 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2565 33 34, g32p_row03_traceSegment_006_2565_0033, g32p_row03_traceSegment_006_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2640 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2632 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2632 8 9, g32p_row03_traceSegment_006_2632_0008, g32p_row03_traceSegment_006_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2649 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2649 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2649 8 9, g32p_row03_traceSegment_006_2649_0008, g32p_row03_traceSegment_006_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2632 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2632 17 17, g32p_row03_traceSegment_006_2632_0017, g32p_row03_traceSegment_006_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2666 8 9, g32p_row03_traceSegment_006_2666_0008, g32p_row03_traceSegment_006_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2683 8 9, g32p_row03_traceSegment_006_2683_0008, g32p_row03_traceSegment_006_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2666 17 17, g32p_row03_traceSegment_006_2666_0017, g32p_row03_traceSegment_006_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 2632 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2632 34 34, g32p_row03_traceSegment_006_2632_0034, g32p_row03_traceSegment_006_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 2565 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2565 67 68, g32p_row03_traceSegment_006_2565_0067, g32p_row03_traceSegment_006_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 2430 270 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2430 135 135, g32p_row03_traceSegment_006_2430_0135, g32p_row03_traceSegment_006_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_006 2160 540 = [15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2160 270 270, g32p_row03_traceSegment_006_2160_0270, g32p_row03_traceSegment_006_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 2700 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2716 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2716 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2716 8 9, g32p_row03_traceSegment_006_2716_0008, g32p_row03_traceSegment_006_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 2700 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2700 16 17, g32p_row03_traceSegment_006_2700_0016, g32p_row03_traceSegment_006_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2741 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2733 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2733 8 9, g32p_row03_traceSegment_006_2733_0008, g32p_row03_traceSegment_006_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2750 8 9, g32p_row03_traceSegment_006_2750_0008, g32p_row03_traceSegment_006_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2733 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2733 17 17, g32p_row03_traceSegment_006_2733_0017, g32p_row03_traceSegment_006_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 2700 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2700 33 34, g32p_row03_traceSegment_006_2700_0033, g32p_row03_traceSegment_006_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2767 8 9, g32p_row03_traceSegment_006_2767_0008, g32p_row03_traceSegment_006_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2792 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2784 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2784 8 9, g32p_row03_traceSegment_006_2784_0008, g32p_row03_traceSegment_006_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2767 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2767 17 17, g32p_row03_traceSegment_006_2767_0017, g32p_row03_traceSegment_006_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2801 8 9, g32p_row03_traceSegment_006_2801_0008, g32p_row03_traceSegment_006_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2818 8 9, g32p_row03_traceSegment_006_2818_0008, g32p_row03_traceSegment_006_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2801 17 17, g32p_row03_traceSegment_006_2801_0017, g32p_row03_traceSegment_006_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 2767 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2767 34 34, g32p_row03_traceSegment_006_2767_0034, g32p_row03_traceSegment_006_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 2700 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2700 67 68, g32p_row03_traceSegment_006_2700_0067, g32p_row03_traceSegment_006_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2851 8 9, g32p_row03_traceSegment_006_2851_0008, g32p_row03_traceSegment_006_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2835 16 17, g32p_row03_traceSegment_006_2835_0016, g32p_row03_traceSegment_006_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2868 8 9, g32p_row03_traceSegment_006_2868_0008, g32p_row03_traceSegment_006_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2885 8 9, g32p_row03_traceSegment_006_2885_0008, g32p_row03_traceSegment_006_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2868 17 17, g32p_row03_traceSegment_006_2868_0017, g32p_row03_traceSegment_006_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2835 33 34, g32p_row03_traceSegment_006_2835_0033, g32p_row03_traceSegment_006_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2902 8 9, g32p_row03_traceSegment_006_2902_0008, g32p_row03_traceSegment_006_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2919 8 9, g32p_row03_traceSegment_006_2919_0008, g32p_row03_traceSegment_006_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2902 17 17, g32p_row03_traceSegment_006_2902_0017, g32p_row03_traceSegment_006_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2936 8 9, g32p_row03_traceSegment_006_2936_0008, g32p_row03_traceSegment_006_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2953 8 9, g32p_row03_traceSegment_006_2953_0008, g32p_row03_traceSegment_006_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2936 17 17, g32p_row03_traceSegment_006_2936_0017, g32p_row03_traceSegment_006_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2902 34 34, g32p_row03_traceSegment_006_2902_0034, g32p_row03_traceSegment_006_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2835 67 68, g32p_row03_traceSegment_006_2835_0067, g32p_row03_traceSegment_006_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 2700 270 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2700 135 135, g32p_row03_traceSegment_006_2700_0135, g32p_row03_traceSegment_006_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2986 8 9, g32p_row03_traceSegment_006_2986_0008, g32p_row03_traceSegment_006_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2970 16 17, g32p_row03_traceSegment_006_2970_0016, g32p_row03_traceSegment_006_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3003 8 9, g32p_row03_traceSegment_006_3003_0008, g32p_row03_traceSegment_006_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3020 8 9, g32p_row03_traceSegment_006_3020_0008, g32p_row03_traceSegment_006_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3003 17 17, g32p_row03_traceSegment_006_3003_0017, g32p_row03_traceSegment_006_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2970 33 34, g32p_row03_traceSegment_006_2970_0033, g32p_row03_traceSegment_006_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3037 8 9, g32p_row03_traceSegment_006_3037_0008, g32p_row03_traceSegment_006_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3054 8 9, g32p_row03_traceSegment_006_3054_0008, g32p_row03_traceSegment_006_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3037 17 17, g32p_row03_traceSegment_006_3037_0017, g32p_row03_traceSegment_006_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3071 8 9, g32p_row03_traceSegment_006_3071_0008, g32p_row03_traceSegment_006_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3088 8 9, g32p_row03_traceSegment_006_3088_0008, g32p_row03_traceSegment_006_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3071 17 17, g32p_row03_traceSegment_006_3071_0017, g32p_row03_traceSegment_006_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3037 34 34, g32p_row03_traceSegment_006_3037_0034, g32p_row03_traceSegment_006_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2970 67 68, g32p_row03_traceSegment_006_2970_0067, g32p_row03_traceSegment_006_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3121 8 9, g32p_row03_traceSegment_006_3121_0008, g32p_row03_traceSegment_006_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3105 16 17, g32p_row03_traceSegment_006_3105_0016, g32p_row03_traceSegment_006_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3138 8 9, g32p_row03_traceSegment_006_3138_0008, g32p_row03_traceSegment_006_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3155 8 9, g32p_row03_traceSegment_006_3155_0008, g32p_row03_traceSegment_006_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3138 17 17, g32p_row03_traceSegment_006_3138_0017, g32p_row03_traceSegment_006_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3105 33 34, g32p_row03_traceSegment_006_3105_0033, g32p_row03_traceSegment_006_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3172 8 9, g32p_row03_traceSegment_006_3172_0008, g32p_row03_traceSegment_006_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3189 8 9, g32p_row03_traceSegment_006_3189_0008, g32p_row03_traceSegment_006_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3172 17 17, g32p_row03_traceSegment_006_3172_0017, g32p_row03_traceSegment_006_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3206 8 9, g32p_row03_traceSegment_006_3206_0008, g32p_row03_traceSegment_006_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3223 8 9, g32p_row03_traceSegment_006_3223_0008, g32p_row03_traceSegment_006_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3206 17 17, g32p_row03_traceSegment_006_3206_0017, g32p_row03_traceSegment_006_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3172 34 34, g32p_row03_traceSegment_006_3172_0034, g32p_row03_traceSegment_006_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3105 67 68, g32p_row03_traceSegment_006_3105_0067, g32p_row03_traceSegment_006_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2970 135 135, g32p_row03_traceSegment_006_2970_0135, g32p_row03_traceSegment_006_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_006 2700 540 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2700 270 270, g32p_row03_traceSegment_006_2700_0270, g32p_row03_traceSegment_006_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_006 2160 1080 = [19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2160 540 540, g32p_row03_traceSegment_006_2160_0540, g32p_row03_traceSegment_006_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3256 8 9, g32p_row03_traceSegment_006_3256_0008, g32p_row03_traceSegment_006_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3240 16 17, g32p_row03_traceSegment_006_3240_0016, g32p_row03_traceSegment_006_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3273 8 9, g32p_row03_traceSegment_006_3273_0008, g32p_row03_traceSegment_006_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3290 8 9, g32p_row03_traceSegment_006_3290_0008, g32p_row03_traceSegment_006_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3273 17 17, g32p_row03_traceSegment_006_3273_0017, g32p_row03_traceSegment_006_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3240 33 34, g32p_row03_traceSegment_006_3240_0033, g32p_row03_traceSegment_006_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3307 8 9, g32p_row03_traceSegment_006_3307_0008, g32p_row03_traceSegment_006_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3324 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3324 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3324 8 9, g32p_row03_traceSegment_006_3324_0008, g32p_row03_traceSegment_006_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3307 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3307 17 17, g32p_row03_traceSegment_006_3307_0017, g32p_row03_traceSegment_006_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3341 8 9, g32p_row03_traceSegment_006_3341_0008, g32p_row03_traceSegment_006_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3358 8 9, g32p_row03_traceSegment_006_3358_0008, g32p_row03_traceSegment_006_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3341 17 17, g32p_row03_traceSegment_006_3341_0017, g32p_row03_traceSegment_006_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 3307 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3307 34 34, g32p_row03_traceSegment_006_3307_0034, g32p_row03_traceSegment_006_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 3240 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3240 67 68, g32p_row03_traceSegment_006_3240_0067, g32p_row03_traceSegment_006_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3391 8 9, g32p_row03_traceSegment_006_3391_0008, g32p_row03_traceSegment_006_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3375 16 17, g32p_row03_traceSegment_006_3375_0016, g32p_row03_traceSegment_006_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3408 8 9, g32p_row03_traceSegment_006_3408_0008, g32p_row03_traceSegment_006_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3425 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3425 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3425 8 9, g32p_row03_traceSegment_006_3425_0008, g32p_row03_traceSegment_006_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3408 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3408 17 17, g32p_row03_traceSegment_006_3408_0017, g32p_row03_traceSegment_006_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 3375 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3375 33 34, g32p_row03_traceSegment_006_3375_0033, g32p_row03_traceSegment_006_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3450 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3442 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3442 8 9, g32p_row03_traceSegment_006_3442_0008, g32p_row03_traceSegment_006_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3459 8 9, g32p_row03_traceSegment_006_3459_0008, g32p_row03_traceSegment_006_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3442 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3442 17 17, g32p_row03_traceSegment_006_3442_0017, g32p_row03_traceSegment_006_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3476 8 9, g32p_row03_traceSegment_006_3476_0008, g32p_row03_traceSegment_006_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3493 8 9, g32p_row03_traceSegment_006_3493_0008, g32p_row03_traceSegment_006_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3476 17 17, g32p_row03_traceSegment_006_3476_0017, g32p_row03_traceSegment_006_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 3442 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3442 34 34, g32p_row03_traceSegment_006_3442_0034, g32p_row03_traceSegment_006_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 3375 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3375 67 68, g32p_row03_traceSegment_006_3375_0067, g32p_row03_traceSegment_006_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 3240 270 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3240 135 135, g32p_row03_traceSegment_006_3240_0135, g32p_row03_traceSegment_006_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3526 8 9, g32p_row03_traceSegment_006_3526_0008, g32p_row03_traceSegment_006_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3510 16 17, g32p_row03_traceSegment_006_3510_0016, g32p_row03_traceSegment_006_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3543 8 9, g32p_row03_traceSegment_006_3543_0008, g32p_row03_traceSegment_006_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3560 8 9, g32p_row03_traceSegment_006_3560_0008, g32p_row03_traceSegment_006_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3543 17 17, g32p_row03_traceSegment_006_3543_0017, g32p_row03_traceSegment_006_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3510 33 34, g32p_row03_traceSegment_006_3510_0033, g32p_row03_traceSegment_006_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3585 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3577 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3577 8 9, g32p_row03_traceSegment_006_3577_0008, g32p_row03_traceSegment_006_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3594 8 9, g32p_row03_traceSegment_006_3594_0008, g32p_row03_traceSegment_006_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3577 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3577 17 17, g32p_row03_traceSegment_006_3577_0017, g32p_row03_traceSegment_006_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3611 8 9, g32p_row03_traceSegment_006_3611_0008, g32p_row03_traceSegment_006_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3628 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3628 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3628 8 9, g32p_row03_traceSegment_006_3628_0008, g32p_row03_traceSegment_006_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3611 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3611 17 17, g32p_row03_traceSegment_006_3611_0017, g32p_row03_traceSegment_006_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 3577 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3577 34 34, g32p_row03_traceSegment_006_3577_0034, g32p_row03_traceSegment_006_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 3510 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3510 67 68, g32p_row03_traceSegment_006_3510_0067, g32p_row03_traceSegment_006_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3661 8 9, g32p_row03_traceSegment_006_3661_0008, g32p_row03_traceSegment_006_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3645 16 17, g32p_row03_traceSegment_006_3645_0016, g32p_row03_traceSegment_006_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3678 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3678 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3678 8 9, g32p_row03_traceSegment_006_3678_0008, g32p_row03_traceSegment_006_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3703 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3695 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3695 8 9, g32p_row03_traceSegment_006_3695_0008, g32p_row03_traceSegment_006_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3678 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3678 17 17, g32p_row03_traceSegment_006_3678_0017, g32p_row03_traceSegment_006_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 3645 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3645 33 34, g32p_row03_traceSegment_006_3645_0033, g32p_row03_traceSegment_006_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3712 8 9, g32p_row03_traceSegment_006_3712_0008, g32p_row03_traceSegment_006_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3729 8 9, g32p_row03_traceSegment_006_3729_0008, g32p_row03_traceSegment_006_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3712 17 17, g32p_row03_traceSegment_006_3712_0017, g32p_row03_traceSegment_006_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3746 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3746 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3746 8 9, g32p_row03_traceSegment_006_3746_0008, g32p_row03_traceSegment_006_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3763 8 9, g32p_row03_traceSegment_006_3763_0008, g32p_row03_traceSegment_006_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3746 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3746 17 17, g32p_row03_traceSegment_006_3746_0017, g32p_row03_traceSegment_006_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 3712 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3712 34 34, g32p_row03_traceSegment_006_3712_0034, g32p_row03_traceSegment_006_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 3645 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3645 67 68, g32p_row03_traceSegment_006_3645_0067, g32p_row03_traceSegment_006_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 3510 270 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3510 135 135, g32p_row03_traceSegment_006_3510_0135, g32p_row03_traceSegment_006_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_006 3240 540 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3240 270 270, g32p_row03_traceSegment_006_3240_0270, g32p_row03_traceSegment_006_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3796 8 9, g32p_row03_traceSegment_006_3796_0008, g32p_row03_traceSegment_006_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3780 16 17, g32p_row03_traceSegment_006_3780_0016, g32p_row03_traceSegment_006_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3813 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3813 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3813 8 9, g32p_row03_traceSegment_006_3813_0008, g32p_row03_traceSegment_006_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3830 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3830 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3830 8 9, g32p_row03_traceSegment_006_3830_0008, g32p_row03_traceSegment_006_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3813 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3813 17 17, g32p_row03_traceSegment_006_3813_0017, g32p_row03_traceSegment_006_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 3780 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3780 33 34, g32p_row03_traceSegment_006_3780_0033, g32p_row03_traceSegment_006_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3847 8 9, g32p_row03_traceSegment_006_3847_0008, g32p_row03_traceSegment_006_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3864 8 9, g32p_row03_traceSegment_006_3864_0008, g32p_row03_traceSegment_006_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3847 17 17, g32p_row03_traceSegment_006_3847_0017, g32p_row03_traceSegment_006_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3881 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3881 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3881 8 9, g32p_row03_traceSegment_006_3881_0008, g32p_row03_traceSegment_006_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3898 8 9, g32p_row03_traceSegment_006_3898_0008, g32p_row03_traceSegment_006_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3881 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3881 17 17, g32p_row03_traceSegment_006_3881_0017, g32p_row03_traceSegment_006_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 3847 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3847 34 34, g32p_row03_traceSegment_006_3847_0034, g32p_row03_traceSegment_006_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 3780 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3780 67 68, g32p_row03_traceSegment_006_3780_0067, g32p_row03_traceSegment_006_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 3915 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3931 8 9, g32p_row03_traceSegment_006_3931_0008, g32p_row03_traceSegment_006_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 3915 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3915 16 17, g32p_row03_traceSegment_006_3915_0016, g32p_row03_traceSegment_006_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3948 8 9, g32p_row03_traceSegment_006_3948_0008, g32p_row03_traceSegment_006_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3965 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3965 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3965 8 9, g32p_row03_traceSegment_006_3965_0008, g32p_row03_traceSegment_006_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3948 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3948 17 17, g32p_row03_traceSegment_006_3948_0017, g32p_row03_traceSegment_006_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 3915 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3915 33 34, g32p_row03_traceSegment_006_3915_0033, g32p_row03_traceSegment_006_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3982 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3982 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3982 8 9, g32p_row03_traceSegment_006_3982_0008, g32p_row03_traceSegment_006_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4007 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 3999 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3999 8 9, g32p_row03_traceSegment_006_3999_0008, g32p_row03_traceSegment_006_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 3982 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3982 17 17, g32p_row03_traceSegment_006_3982_0017, g32p_row03_traceSegment_006_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4016 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4016 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4016 8 9, g32p_row03_traceSegment_006_4016_0008, g32p_row03_traceSegment_006_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4033 8 9, g32p_row03_traceSegment_006_4033_0008, g32p_row03_traceSegment_006_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 4016 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4016 17 17, g32p_row03_traceSegment_006_4016_0017, g32p_row03_traceSegment_006_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 3982 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3982 34 34, g32p_row03_traceSegment_006_3982_0034, g32p_row03_traceSegment_006_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 3915 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3915 67 68, g32p_row03_traceSegment_006_3915_0067, g32p_row03_traceSegment_006_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 3780 270 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3780 135 135, g32p_row03_traceSegment_006_3780_0135, g32p_row03_traceSegment_006_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4066 8 9, g32p_row03_traceSegment_006_4066_0008, g32p_row03_traceSegment_006_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4050 16 17, g32p_row03_traceSegment_006_4050_0016, g32p_row03_traceSegment_006_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4083 8 9, g32p_row03_traceSegment_006_4083_0008, g32p_row03_traceSegment_006_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4100 8 9, g32p_row03_traceSegment_006_4100_0008, g32p_row03_traceSegment_006_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4083 17 17, g32p_row03_traceSegment_006_4083_0017, g32p_row03_traceSegment_006_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4050 33 34, g32p_row03_traceSegment_006_4050_0033, g32p_row03_traceSegment_006_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4117 8 9, g32p_row03_traceSegment_006_4117_0008, g32p_row03_traceSegment_006_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4134 8 9, g32p_row03_traceSegment_006_4134_0008, g32p_row03_traceSegment_006_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4117 17 17, g32p_row03_traceSegment_006_4117_0017, g32p_row03_traceSegment_006_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4151 8 9, g32p_row03_traceSegment_006_4151_0008, g32p_row03_traceSegment_006_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4168 8 9, g32p_row03_traceSegment_006_4168_0008, g32p_row03_traceSegment_006_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4151 17 17, g32p_row03_traceSegment_006_4151_0017, g32p_row03_traceSegment_006_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4117 34 34, g32p_row03_traceSegment_006_4117_0034, g32p_row03_traceSegment_006_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4050 67 68, g32p_row03_traceSegment_006_4050_0067, g32p_row03_traceSegment_006_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_006 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4201 8 9, g32p_row03_traceSegment_006_4201_0008, g32p_row03_traceSegment_006_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_006 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4185 16 17, g32p_row03_traceSegment_006_4185_0016, g32p_row03_traceSegment_006_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4218 8 9, g32p_row03_traceSegment_006_4218_0008, g32p_row03_traceSegment_006_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4235 8 9, g32p_row03_traceSegment_006_4235_0008, g32p_row03_traceSegment_006_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4218 17 17, g32p_row03_traceSegment_006_4218_0017, g32p_row03_traceSegment_006_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_006 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4185 33 34, g32p_row03_traceSegment_006_4185_0033, g32p_row03_traceSegment_006_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4252 8 9, g32p_row03_traceSegment_006_4252_0008, g32p_row03_traceSegment_006_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4269 8 9, g32p_row03_traceSegment_006_4269_0008, g32p_row03_traceSegment_006_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4252 17 17, g32p_row03_traceSegment_006_4252_0017, g32p_row03_traceSegment_006_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4286 8 9, g32p_row03_traceSegment_006_4286_0008, g32p_row03_traceSegment_006_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_006 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_006 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_006_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_006 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4303 8 9, g32p_row03_traceSegment_006_4303_0008, g32p_row03_traceSegment_006_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_006 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4286 17 17, g32p_row03_traceSegment_006_4286_0017, g32p_row03_traceSegment_006_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_006 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4252 34 34, g32p_row03_traceSegment_006_4252_0034, g32p_row03_traceSegment_006_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_006 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4185 67 68, g32p_row03_traceSegment_006_4185_0067, g32p_row03_traceSegment_006_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_006_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_006 4050 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 4050 135 135, g32p_row03_traceSegment_006_4050_0135, g32p_row03_traceSegment_006_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_006 3780 540 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3780 270 270, g32p_row03_traceSegment_006_3780_0270, g32p_row03_traceSegment_006_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_006_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_006 3240 1080 = [16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 3240 540 540, g32p_row03_traceSegment_006_3240_0540, g32p_row03_traceSegment_006_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_006_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_006 2160 2160 = [35] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 2160 1080 1080, g32p_row03_traceSegment_006_2160_1080, g32p_row03_traceSegment_006_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_006_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_006 0 4320 = [40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_006 0 2160 2160, g32p_row03_traceSegment_006_0000_2160, g32p_row03_traceSegment_006_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 6 = [40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_006_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_010 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 10 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_010_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 16 8 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 16 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 16 8 9, g32p_row03_traceSegment_010_0016_0008, g32p_row03_traceSegment_010_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 0 33 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 0 16 17, g32p_row03_traceSegment_010_0000_0016, g32p_row03_traceSegment_010_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 33 8 9, g32p_row03_traceSegment_010_0033_0008, g32p_row03_traceSegment_010_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 50 8 9, g32p_row03_traceSegment_010_0050_0008, g32p_row03_traceSegment_010_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 33 17 17, g32p_row03_traceSegment_010_0033_0017, g32p_row03_traceSegment_010_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 0 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 0 33 34, g32p_row03_traceSegment_010_0000_0033, g32p_row03_traceSegment_010_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 67 8 9, g32p_row03_traceSegment_010_0067_0008, g32p_row03_traceSegment_010_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 84 8 9, g32p_row03_traceSegment_010_0084_0008, g32p_row03_traceSegment_010_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 67 17 17, g32p_row03_traceSegment_010_0067_0017, g32p_row03_traceSegment_010_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 101 8 9, g32p_row03_traceSegment_010_0101_0008, g32p_row03_traceSegment_010_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 118 8 9, g32p_row03_traceSegment_010_0118_0008, g32p_row03_traceSegment_010_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 101 17 17, g32p_row03_traceSegment_010_0101_0017, g32p_row03_traceSegment_010_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 67 34 34, g32p_row03_traceSegment_010_0067_0034, g32p_row03_traceSegment_010_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 0 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 0 67 68, g32p_row03_traceSegment_010_0000_0067, g32p_row03_traceSegment_010_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 135 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 151 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 151 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 151 8 9, g32p_row03_traceSegment_010_0151_0008, g32p_row03_traceSegment_010_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 135 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 135 16 17, g32p_row03_traceSegment_010_0135_0016, g32p_row03_traceSegment_010_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 168 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 176 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 168 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 168 8 9, g32p_row03_traceSegment_010_0168_0008, g32p_row03_traceSegment_010_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 193 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 185 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 185 8 9, g32p_row03_traceSegment_010_0185_0008, g32p_row03_traceSegment_010_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 168 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 168 17 17, g32p_row03_traceSegment_010_0168_0017, g32p_row03_traceSegment_010_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 135 67 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 135 33 34, g32p_row03_traceSegment_010_0135_0033, g32p_row03_traceSegment_010_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 210 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 202 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 202 8 9, g32p_row03_traceSegment_010_0202_0008, g32p_row03_traceSegment_010_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 219 8 9, g32p_row03_traceSegment_010_0219_0008, g32p_row03_traceSegment_010_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 202 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 202 17 17, g32p_row03_traceSegment_010_0202_0017, g32p_row03_traceSegment_010_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 236 8 9, g32p_row03_traceSegment_010_0236_0008, g32p_row03_traceSegment_010_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 253 8 9, g32p_row03_traceSegment_010_0253_0008, g32p_row03_traceSegment_010_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 236 17 17, g32p_row03_traceSegment_010_0236_0017, g32p_row03_traceSegment_010_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 202 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 202 34 34, g32p_row03_traceSegment_010_0202_0034, g32p_row03_traceSegment_010_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 135 135 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 135 67 68, g32p_row03_traceSegment_010_0135_0067, g32p_row03_traceSegment_010_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 0 270 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 0 135 135, g32p_row03_traceSegment_010_0000_0135, g32p_row03_traceSegment_010_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 286 8 9, g32p_row03_traceSegment_010_0286_0008, g32p_row03_traceSegment_010_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 270 16 17, g32p_row03_traceSegment_010_0270_0016, g32p_row03_traceSegment_010_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 311 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 303 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 303 8 9, g32p_row03_traceSegment_010_0303_0008, g32p_row03_traceSegment_010_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 320 8 9, g32p_row03_traceSegment_010_0320_0008, g32p_row03_traceSegment_010_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 303 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 303 17 17, g32p_row03_traceSegment_010_0303_0017, g32p_row03_traceSegment_010_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 270 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 270 33 34, g32p_row03_traceSegment_010_0270_0033, g32p_row03_traceSegment_010_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 337 8 9, g32p_row03_traceSegment_010_0337_0008, g32p_row03_traceSegment_010_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 362 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 354 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 354 8 9, g32p_row03_traceSegment_010_0354_0008, g32p_row03_traceSegment_010_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 337 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 337 17 17, g32p_row03_traceSegment_010_0337_0017, g32p_row03_traceSegment_010_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 379 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 371 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 371 8 9, g32p_row03_traceSegment_010_0371_0008, g32p_row03_traceSegment_010_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 396 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 388 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 388 8 9, g32p_row03_traceSegment_010_0388_0008, g32p_row03_traceSegment_010_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 371 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 371 17 17, g32p_row03_traceSegment_010_0371_0017, g32p_row03_traceSegment_010_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 337 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 337 34 34, g32p_row03_traceSegment_010_0337_0034, g32p_row03_traceSegment_010_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 270 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 270 67 68, g32p_row03_traceSegment_010_0270_0067, g32p_row03_traceSegment_010_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 429 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 421 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 421 8 9, g32p_row03_traceSegment_010_0421_0008, g32p_row03_traceSegment_010_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 405 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 405 16 17, g32p_row03_traceSegment_010_0405_0016, g32p_row03_traceSegment_010_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 446 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 438 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 438 8 9, g32p_row03_traceSegment_010_0438_0008, g32p_row03_traceSegment_010_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 455 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 463 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 455 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 455 8 9, g32p_row03_traceSegment_010_0455_0008, g32p_row03_traceSegment_010_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 438 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 438 17 17, g32p_row03_traceSegment_010_0438_0017, g32p_row03_traceSegment_010_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 405 67 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 405 33 34, g32p_row03_traceSegment_010_0405_0033, g32p_row03_traceSegment_010_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 480 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 472 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 472 8 9, g32p_row03_traceSegment_010_0472_0008, g32p_row03_traceSegment_010_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 489 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 497 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 489 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 489 8 9, g32p_row03_traceSegment_010_0489_0008, g32p_row03_traceSegment_010_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 472 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 472 17 17, g32p_row03_traceSegment_010_0472_0017, g32p_row03_traceSegment_010_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 506 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 514 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 506 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 506 8 9, g32p_row03_traceSegment_010_0506_0008, g32p_row03_traceSegment_010_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 523 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 523 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 523 8 9, g32p_row03_traceSegment_010_0523_0008, g32p_row03_traceSegment_010_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 506 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 506 17 17, g32p_row03_traceSegment_010_0506_0017, g32p_row03_traceSegment_010_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 472 68 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 472 34 34, g32p_row03_traceSegment_010_0472_0034, g32p_row03_traceSegment_010_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 405 135 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 405 67 68, g32p_row03_traceSegment_010_0405_0067, g32p_row03_traceSegment_010_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 270 270 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 270 135 135, g32p_row03_traceSegment_010_0270_0135, g32p_row03_traceSegment_010_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_010 0 540 = [0, 0, 0, 0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 0 270 270, g32p_row03_traceSegment_010_0000_0270, g32p_row03_traceSegment_010_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 540 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 564 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 556 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 556 8 9, g32p_row03_traceSegment_010_0556_0008, g32p_row03_traceSegment_010_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 540 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 540 16 17, g32p_row03_traceSegment_010_0540_0016, g32p_row03_traceSegment_010_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 581 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 573 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 573 8 9, g32p_row03_traceSegment_010_0573_0008, g32p_row03_traceSegment_010_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 598 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 590 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 590 8 9, g32p_row03_traceSegment_010_0590_0008, g32p_row03_traceSegment_010_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 573 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 573 17 17, g32p_row03_traceSegment_010_0573_0017, g32p_row03_traceSegment_010_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 540 67 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 540 33 34, g32p_row03_traceSegment_010_0540_0033, g32p_row03_traceSegment_010_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 607 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 615 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 607 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 607 8 9, g32p_row03_traceSegment_010_0607_0008, g32p_row03_traceSegment_010_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 624 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 632 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 624 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 624 8 9, g32p_row03_traceSegment_010_0624_0008, g32p_row03_traceSegment_010_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 607 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 607 17 17, g32p_row03_traceSegment_010_0607_0017, g32p_row03_traceSegment_010_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 649 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 641 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 641 8 9, g32p_row03_traceSegment_010_0641_0008, g32p_row03_traceSegment_010_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 658 8 9, g32p_row03_traceSegment_010_0658_0008, g32p_row03_traceSegment_010_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 641 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 641 17 17, g32p_row03_traceSegment_010_0641_0017, g32p_row03_traceSegment_010_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 607 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 607 34 34, g32p_row03_traceSegment_010_0607_0034, g32p_row03_traceSegment_010_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 540 135 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 540 67 68, g32p_row03_traceSegment_010_0540_0067, g32p_row03_traceSegment_010_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 675 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 691 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 691 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 691 8 9, g32p_row03_traceSegment_010_0691_0008, g32p_row03_traceSegment_010_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 675 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 675 16 17, g32p_row03_traceSegment_010_0675_0016, g32p_row03_traceSegment_010_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 708 8 9, g32p_row03_traceSegment_010_0708_0008, g32p_row03_traceSegment_010_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 725 8 9, g32p_row03_traceSegment_010_0725_0008, g32p_row03_traceSegment_010_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 708 17 17, g32p_row03_traceSegment_010_0708_0017, g32p_row03_traceSegment_010_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 675 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 675 33 34, g32p_row03_traceSegment_010_0675_0033, g32p_row03_traceSegment_010_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 742 8 9, g32p_row03_traceSegment_010_0742_0008, g32p_row03_traceSegment_010_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 759 8 9, g32p_row03_traceSegment_010_0759_0008, g32p_row03_traceSegment_010_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 742 17 17, g32p_row03_traceSegment_010_0742_0017, g32p_row03_traceSegment_010_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 776 8 9, g32p_row03_traceSegment_010_0776_0008, g32p_row03_traceSegment_010_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 793 8 9, g32p_row03_traceSegment_010_0793_0008, g32p_row03_traceSegment_010_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 776 17 17, g32p_row03_traceSegment_010_0776_0017, g32p_row03_traceSegment_010_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 742 34 34, g32p_row03_traceSegment_010_0742_0034, g32p_row03_traceSegment_010_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 675 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 675 67 68, g32p_row03_traceSegment_010_0675_0067, g32p_row03_traceSegment_010_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 540 270 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 540 135 135, g32p_row03_traceSegment_010_0540_0135, g32p_row03_traceSegment_010_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 826 8 9, g32p_row03_traceSegment_010_0826_0008, g32p_row03_traceSegment_010_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 810 16 17, g32p_row03_traceSegment_010_0810_0016, g32p_row03_traceSegment_010_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 843 8 9, g32p_row03_traceSegment_010_0843_0008, g32p_row03_traceSegment_010_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 860 8 9, g32p_row03_traceSegment_010_0860_0008, g32p_row03_traceSegment_010_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 843 17 17, g32p_row03_traceSegment_010_0843_0017, g32p_row03_traceSegment_010_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 810 33 34, g32p_row03_traceSegment_010_0810_0033, g32p_row03_traceSegment_010_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 877 8 9, g32p_row03_traceSegment_010_0877_0008, g32p_row03_traceSegment_010_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 894 8 9, g32p_row03_traceSegment_010_0894_0008, g32p_row03_traceSegment_010_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 877 17 17, g32p_row03_traceSegment_010_0877_0017, g32p_row03_traceSegment_010_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 911 8 9, g32p_row03_traceSegment_010_0911_0008, g32p_row03_traceSegment_010_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 928 8 9, g32p_row03_traceSegment_010_0928_0008, g32p_row03_traceSegment_010_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 911 17 17, g32p_row03_traceSegment_010_0911_0017, g32p_row03_traceSegment_010_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 877 34 34, g32p_row03_traceSegment_010_0877_0034, g32p_row03_traceSegment_010_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 810 67 68, g32p_row03_traceSegment_010_0810_0067, g32p_row03_traceSegment_010_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 945 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 961 8 9, g32p_row03_traceSegment_010_0961_0008, g32p_row03_traceSegment_010_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 945 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 945 16 17, g32p_row03_traceSegment_010_0945_0016, g32p_row03_traceSegment_010_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 978 8 9, g32p_row03_traceSegment_010_0978_0008, g32p_row03_traceSegment_010_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1003 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 995 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 995 8 9, g32p_row03_traceSegment_010_0995_0008, g32p_row03_traceSegment_010_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 978 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 978 17 17, g32p_row03_traceSegment_010_0978_0017, g32p_row03_traceSegment_010_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 945 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 945 33 34, g32p_row03_traceSegment_010_0945_0033, g32p_row03_traceSegment_010_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1012 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1012 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1012 8 9, g32p_row03_traceSegment_010_1012_0008, g32p_row03_traceSegment_010_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1029 8 9, g32p_row03_traceSegment_010_1029_0008, g32p_row03_traceSegment_010_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1012 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1012 17 17, g32p_row03_traceSegment_010_1012_0017, g32p_row03_traceSegment_010_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1046 8 9, g32p_row03_traceSegment_010_1046_0008, g32p_row03_traceSegment_010_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1063 8 9, g32p_row03_traceSegment_010_1063_0008, g32p_row03_traceSegment_010_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1046 17 17, g32p_row03_traceSegment_010_1046_0017, g32p_row03_traceSegment_010_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 1012 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1012 34 34, g32p_row03_traceSegment_010_1012_0034, g32p_row03_traceSegment_010_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 945 135 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 945 67 68, g32p_row03_traceSegment_010_0945_0067, g32p_row03_traceSegment_010_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 810 270 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 810 135 135, g32p_row03_traceSegment_010_0810_0135, g32p_row03_traceSegment_010_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_010 540 540 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 540 270 270, g32p_row03_traceSegment_010_0540_0270, g32p_row03_traceSegment_010_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_010 0 1080 = [0, 0, 0, 0, 0, 42] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 0 540 540, g32p_row03_traceSegment_010_0000_0540, g32p_row03_traceSegment_010_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1104 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1096 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1096 8 9, g32p_row03_traceSegment_010_1096_0008, g32p_row03_traceSegment_010_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 1080 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1080 16 17, g32p_row03_traceSegment_010_1080_0016, g32p_row03_traceSegment_010_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1113 8 9, g32p_row03_traceSegment_010_1113_0008, g32p_row03_traceSegment_010_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1138 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1130 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1130 8 9, g32p_row03_traceSegment_010_1130_0008, g32p_row03_traceSegment_010_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1113 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1113 17 17, g32p_row03_traceSegment_010_1113_0017, g32p_row03_traceSegment_010_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 1080 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1080 33 34, g32p_row03_traceSegment_010_1080_0033, g32p_row03_traceSegment_010_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1147 8 9, g32p_row03_traceSegment_010_1147_0008, g32p_row03_traceSegment_010_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1164 8 9, g32p_row03_traceSegment_010_1164_0008, g32p_row03_traceSegment_010_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1147 17 17, g32p_row03_traceSegment_010_1147_0017, g32p_row03_traceSegment_010_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1181 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1181 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1181 8 9, g32p_row03_traceSegment_010_1181_0008, g32p_row03_traceSegment_010_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1198 8 9, g32p_row03_traceSegment_010_1198_0008, g32p_row03_traceSegment_010_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1181 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1181 17 17, g32p_row03_traceSegment_010_1181_0017, g32p_row03_traceSegment_010_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 1147 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1147 34 34, g32p_row03_traceSegment_010_1147_0034, g32p_row03_traceSegment_010_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 1080 135 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1080 67 68, g32p_row03_traceSegment_010_1080_0067, g32p_row03_traceSegment_010_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1231 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1239 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1231 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1231 8 9, g32p_row03_traceSegment_010_1231_0008, g32p_row03_traceSegment_010_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 1215 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1215 16 17, g32p_row03_traceSegment_010_1215_0016, g32p_row03_traceSegment_010_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1256 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1248 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1248 8 9, g32p_row03_traceSegment_010_1248_0008, g32p_row03_traceSegment_010_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1273 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1265 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1265 8 9, g32p_row03_traceSegment_010_1265_0008, g32p_row03_traceSegment_010_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1248 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1248 17 17, g32p_row03_traceSegment_010_1248_0017, g32p_row03_traceSegment_010_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 1215 67 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1215 33 34, g32p_row03_traceSegment_010_1215_0033, g32p_row03_traceSegment_010_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1282 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1282 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1282 8 9, g32p_row03_traceSegment_010_1282_0008, g32p_row03_traceSegment_010_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1299 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1307 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1299 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1299 8 9, g32p_row03_traceSegment_010_1299_0008, g32p_row03_traceSegment_010_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1282 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1282 17 17, g32p_row03_traceSegment_010_1282_0017, g32p_row03_traceSegment_010_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1316 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1324 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1316 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1316 8 9, g32p_row03_traceSegment_010_1316_0008, g32p_row03_traceSegment_010_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1333 8 9, g32p_row03_traceSegment_010_1333_0008, g32p_row03_traceSegment_010_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1316 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1316 17 17, g32p_row03_traceSegment_010_1316_0017, g32p_row03_traceSegment_010_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 1282 68 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1282 34 34, g32p_row03_traceSegment_010_1282_0034, g32p_row03_traceSegment_010_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 1215 135 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1215 67 68, g32p_row03_traceSegment_010_1215_0067, g32p_row03_traceSegment_010_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 1080 270 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1080 135 135, g32p_row03_traceSegment_010_1080_0135, g32p_row03_traceSegment_010_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1366 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1366 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1366 8 9, g32p_row03_traceSegment_010_1366_0008, g32p_row03_traceSegment_010_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 1350 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1350 16 17, g32p_row03_traceSegment_010_1350_0016, g32p_row03_traceSegment_010_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1383 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1391 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1383 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1383 8 9, g32p_row03_traceSegment_010_1383_0008, g32p_row03_traceSegment_010_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1408 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1400 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1400 8 9, g32p_row03_traceSegment_010_1400_0008, g32p_row03_traceSegment_010_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1383 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1383 17 17, g32p_row03_traceSegment_010_1383_0017, g32p_row03_traceSegment_010_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 1350 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1350 33 34, g32p_row03_traceSegment_010_1350_0033, g32p_row03_traceSegment_010_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1417 8 9, g32p_row03_traceSegment_010_1417_0008, g32p_row03_traceSegment_010_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1434 8 9, g32p_row03_traceSegment_010_1434_0008, g32p_row03_traceSegment_010_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1417 17 17, g32p_row03_traceSegment_010_1417_0017, g32p_row03_traceSegment_010_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1451 8 9, g32p_row03_traceSegment_010_1451_0008, g32p_row03_traceSegment_010_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1468 8 9, g32p_row03_traceSegment_010_1468_0008, g32p_row03_traceSegment_010_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1451 17 17, g32p_row03_traceSegment_010_1451_0017, g32p_row03_traceSegment_010_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1417 34 34, g32p_row03_traceSegment_010_1417_0034, g32p_row03_traceSegment_010_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 1350 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1350 67 68, g32p_row03_traceSegment_010_1350_0067, g32p_row03_traceSegment_010_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 1485 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1501 8 9, g32p_row03_traceSegment_010_1501_0008, g32p_row03_traceSegment_010_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 1485 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1485 16 17, g32p_row03_traceSegment_010_1485_0016, g32p_row03_traceSegment_010_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1518 8 9, g32p_row03_traceSegment_010_1518_0008, g32p_row03_traceSegment_010_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1543 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1535 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1535 8 9, g32p_row03_traceSegment_010_1535_0008, g32p_row03_traceSegment_010_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1518 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1518 17 17, g32p_row03_traceSegment_010_1518_0017, g32p_row03_traceSegment_010_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 1485 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1485 33 34, g32p_row03_traceSegment_010_1485_0033, g32p_row03_traceSegment_010_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1552 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1552 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1552 8 9, g32p_row03_traceSegment_010_1552_0008, g32p_row03_traceSegment_010_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1569 8 9, g32p_row03_traceSegment_010_1569_0008, g32p_row03_traceSegment_010_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1552 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1552 17 17, g32p_row03_traceSegment_010_1552_0017, g32p_row03_traceSegment_010_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1586 8 9, g32p_row03_traceSegment_010_1586_0008, g32p_row03_traceSegment_010_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1603 8 9, g32p_row03_traceSegment_010_1603_0008, g32p_row03_traceSegment_010_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1586 17 17, g32p_row03_traceSegment_010_1586_0017, g32p_row03_traceSegment_010_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 1552 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1552 34 34, g32p_row03_traceSegment_010_1552_0034, g32p_row03_traceSegment_010_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 1485 135 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1485 67 68, g32p_row03_traceSegment_010_1485_0067, g32p_row03_traceSegment_010_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 1350 270 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1350 135 135, g32p_row03_traceSegment_010_1350_0135, g32p_row03_traceSegment_010_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_010 1080 540 = [0, 0, 0, 0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1080 270 270, g32p_row03_traceSegment_010_1080_0270, g32p_row03_traceSegment_010_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 1620 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1636 8 9, g32p_row03_traceSegment_010_1636_0008, g32p_row03_traceSegment_010_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 1620 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1620 16 17, g32p_row03_traceSegment_010_1620_0016, g32p_row03_traceSegment_010_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1653 8 9, g32p_row03_traceSegment_010_1653_0008, g32p_row03_traceSegment_010_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1678 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1670 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1670 8 9, g32p_row03_traceSegment_010_1670_0008, g32p_row03_traceSegment_010_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1653 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1653 17 17, g32p_row03_traceSegment_010_1653_0017, g32p_row03_traceSegment_010_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 1620 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1620 33 34, g32p_row03_traceSegment_010_1620_0033, g32p_row03_traceSegment_010_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1695 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1687 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1687 8 9, g32p_row03_traceSegment_010_1687_0008, g32p_row03_traceSegment_010_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1704 8 9, g32p_row03_traceSegment_010_1704_0008, g32p_row03_traceSegment_010_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1687 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1687 17 17, g32p_row03_traceSegment_010_1687_0017, g32p_row03_traceSegment_010_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1721 8 9, g32p_row03_traceSegment_010_1721_0008, g32p_row03_traceSegment_010_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1738 8 9, g32p_row03_traceSegment_010_1738_0008, g32p_row03_traceSegment_010_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1721 17 17, g32p_row03_traceSegment_010_1721_0017, g32p_row03_traceSegment_010_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 1687 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1687 34 34, g32p_row03_traceSegment_010_1687_0034, g32p_row03_traceSegment_010_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 1620 135 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1620 67 68, g32p_row03_traceSegment_010_1620_0067, g32p_row03_traceSegment_010_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 1755 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1771 8 9, g32p_row03_traceSegment_010_1771_0008, g32p_row03_traceSegment_010_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 1755 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1755 16 17, g32p_row03_traceSegment_010_1755_0016, g32p_row03_traceSegment_010_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1788 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1788 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1788 8 9, g32p_row03_traceSegment_010_1788_0008, g32p_row03_traceSegment_010_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1805 8 9, g32p_row03_traceSegment_010_1805_0008, g32p_row03_traceSegment_010_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1788 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1788 17 17, g32p_row03_traceSegment_010_1788_0017, g32p_row03_traceSegment_010_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 1755 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1755 33 34, g32p_row03_traceSegment_010_1755_0033, g32p_row03_traceSegment_010_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1822 8 9, g32p_row03_traceSegment_010_1822_0008, g32p_row03_traceSegment_010_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1839 8 9, g32p_row03_traceSegment_010_1839_0008, g32p_row03_traceSegment_010_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1822 17 17, g32p_row03_traceSegment_010_1822_0017, g32p_row03_traceSegment_010_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1856 8 9, g32p_row03_traceSegment_010_1856_0008, g32p_row03_traceSegment_010_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1873 8 9, g32p_row03_traceSegment_010_1873_0008, g32p_row03_traceSegment_010_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1856 17 17, g32p_row03_traceSegment_010_1856_0017, g32p_row03_traceSegment_010_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1822 34 34, g32p_row03_traceSegment_010_1822_0034, g32p_row03_traceSegment_010_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 1755 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1755 67 68, g32p_row03_traceSegment_010_1755_0067, g32p_row03_traceSegment_010_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 1620 270 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1620 135 135, g32p_row03_traceSegment_010_1620_0135, g32p_row03_traceSegment_010_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1906 8 9, g32p_row03_traceSegment_010_1906_0008, g32p_row03_traceSegment_010_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1890 16 17, g32p_row03_traceSegment_010_1890_0016, g32p_row03_traceSegment_010_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1923 8 9, g32p_row03_traceSegment_010_1923_0008, g32p_row03_traceSegment_010_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1940 8 9, g32p_row03_traceSegment_010_1940_0008, g32p_row03_traceSegment_010_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1923 17 17, g32p_row03_traceSegment_010_1923_0017, g32p_row03_traceSegment_010_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1890 33 34, g32p_row03_traceSegment_010_1890_0033, g32p_row03_traceSegment_010_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1957 8 9, g32p_row03_traceSegment_010_1957_0008, g32p_row03_traceSegment_010_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1974 8 9, g32p_row03_traceSegment_010_1974_0008, g32p_row03_traceSegment_010_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1957 17 17, g32p_row03_traceSegment_010_1957_0017, g32p_row03_traceSegment_010_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1991 8 9, g32p_row03_traceSegment_010_1991_0008, g32p_row03_traceSegment_010_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2008 8 9, g32p_row03_traceSegment_010_2008_0008, g32p_row03_traceSegment_010_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1991 17 17, g32p_row03_traceSegment_010_1991_0017, g32p_row03_traceSegment_010_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1957 34 34, g32p_row03_traceSegment_010_1957_0034, g32p_row03_traceSegment_010_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1890 67 68, g32p_row03_traceSegment_010_1890_0067, g32p_row03_traceSegment_010_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2041 8 9, g32p_row03_traceSegment_010_2041_0008, g32p_row03_traceSegment_010_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2025 16 17, g32p_row03_traceSegment_010_2025_0016, g32p_row03_traceSegment_010_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2058 8 9, g32p_row03_traceSegment_010_2058_0008, g32p_row03_traceSegment_010_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2075 8 9, g32p_row03_traceSegment_010_2075_0008, g32p_row03_traceSegment_010_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2058 17 17, g32p_row03_traceSegment_010_2058_0017, g32p_row03_traceSegment_010_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2025 33 34, g32p_row03_traceSegment_010_2025_0033, g32p_row03_traceSegment_010_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2092 8 9, g32p_row03_traceSegment_010_2092_0008, g32p_row03_traceSegment_010_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2117 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2109 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2109 8 9, g32p_row03_traceSegment_010_2109_0008, g32p_row03_traceSegment_010_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2092 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2092 17 17, g32p_row03_traceSegment_010_2092_0017, g32p_row03_traceSegment_010_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2126 8 9, g32p_row03_traceSegment_010_2126_0008, g32p_row03_traceSegment_010_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2143 8 9, g32p_row03_traceSegment_010_2143_0008, g32p_row03_traceSegment_010_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2126 17 17, g32p_row03_traceSegment_010_2126_0017, g32p_row03_traceSegment_010_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 2092 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2092 34 34, g32p_row03_traceSegment_010_2092_0034, g32p_row03_traceSegment_010_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 2025 135 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2025 67 68, g32p_row03_traceSegment_010_2025_0067, g32p_row03_traceSegment_010_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 1890 270 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1890 135 135, g32p_row03_traceSegment_010_1890_0135, g32p_row03_traceSegment_010_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_010 1620 540 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1620 270 270, g32p_row03_traceSegment_010_1620_0270, g32p_row03_traceSegment_010_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_010_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_010 1080 1080 = [0, 0, 0, 0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 1080 540 540, g32p_row03_traceSegment_010_1080_0540, g32p_row03_traceSegment_010_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_010 0 2160 = [0, 0, 0, 0, 0, 70] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 0 1080 1080, g32p_row03_traceSegment_010_0000_1080, g32p_row03_traceSegment_010_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2176 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2176 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2176 8 9, g32p_row03_traceSegment_010_2176_0008, g32p_row03_traceSegment_010_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 2160 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2160 16 17, g32p_row03_traceSegment_010_2160_0016, g32p_row03_traceSegment_010_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2193 8 9, g32p_row03_traceSegment_010_2193_0008, g32p_row03_traceSegment_010_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2210 8 9, g32p_row03_traceSegment_010_2210_0008, g32p_row03_traceSegment_010_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2193 17 17, g32p_row03_traceSegment_010_2193_0017, g32p_row03_traceSegment_010_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 2160 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2160 33 34, g32p_row03_traceSegment_010_2160_0033, g32p_row03_traceSegment_010_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2227 8 9, g32p_row03_traceSegment_010_2227_0008, g32p_row03_traceSegment_010_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2252 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2244 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2244 8 9, g32p_row03_traceSegment_010_2244_0008, g32p_row03_traceSegment_010_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2227 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2227 17 17, g32p_row03_traceSegment_010_2227_0017, g32p_row03_traceSegment_010_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2269 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2261 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2261 8 9, g32p_row03_traceSegment_010_2261_0008, g32p_row03_traceSegment_010_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2278 8 9, g32p_row03_traceSegment_010_2278_0008, g32p_row03_traceSegment_010_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2261 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2261 17 17, g32p_row03_traceSegment_010_2261_0017, g32p_row03_traceSegment_010_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 2227 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2227 34 34, g32p_row03_traceSegment_010_2227_0034, g32p_row03_traceSegment_010_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 2160 135 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2160 67 68, g32p_row03_traceSegment_010_2160_0067, g32p_row03_traceSegment_010_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2319 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2311 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2311 8 9, g32p_row03_traceSegment_010_2311_0008, g32p_row03_traceSegment_010_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 2295 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2295 16 17, g32p_row03_traceSegment_010_2295_0016, g32p_row03_traceSegment_010_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2336 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2328 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2328 8 9, g32p_row03_traceSegment_010_2328_0008, g32p_row03_traceSegment_010_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2345 8 9, g32p_row03_traceSegment_010_2345_0008, g32p_row03_traceSegment_010_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2328 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2328 17 17, g32p_row03_traceSegment_010_2328_0017, g32p_row03_traceSegment_010_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 2295 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2295 33 34, g32p_row03_traceSegment_010_2295_0033, g32p_row03_traceSegment_010_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2362 8 9, g32p_row03_traceSegment_010_2362_0008, g32p_row03_traceSegment_010_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2379 8 9, g32p_row03_traceSegment_010_2379_0008, g32p_row03_traceSegment_010_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2362 17 17, g32p_row03_traceSegment_010_2362_0017, g32p_row03_traceSegment_010_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2404 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2396 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2396 8 9, g32p_row03_traceSegment_010_2396_0008, g32p_row03_traceSegment_010_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2413 8 9, g32p_row03_traceSegment_010_2413_0008, g32p_row03_traceSegment_010_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2396 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2396 17 17, g32p_row03_traceSegment_010_2396_0017, g32p_row03_traceSegment_010_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 2362 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2362 34 34, g32p_row03_traceSegment_010_2362_0034, g32p_row03_traceSegment_010_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 2295 135 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2295 67 68, g32p_row03_traceSegment_010_2295_0067, g32p_row03_traceSegment_010_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 2160 270 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2160 135 135, g32p_row03_traceSegment_010_2160_0135, g32p_row03_traceSegment_010_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2454 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2446 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2446 8 9, g32p_row03_traceSegment_010_2446_0008, g32p_row03_traceSegment_010_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 2430 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2430 16 17, g32p_row03_traceSegment_010_2430_0016, g32p_row03_traceSegment_010_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2463 8 9, g32p_row03_traceSegment_010_2463_0008, g32p_row03_traceSegment_010_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2488 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2480 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2480 8 9, g32p_row03_traceSegment_010_2480_0008, g32p_row03_traceSegment_010_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2463 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2463 17 17, g32p_row03_traceSegment_010_2463_0017, g32p_row03_traceSegment_010_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 2430 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2430 33 34, g32p_row03_traceSegment_010_2430_0033, g32p_row03_traceSegment_010_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2497 8 9, g32p_row03_traceSegment_010_2497_0008, g32p_row03_traceSegment_010_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2522 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2514 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2514 8 9, g32p_row03_traceSegment_010_2514_0008, g32p_row03_traceSegment_010_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2497 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2497 17 17, g32p_row03_traceSegment_010_2497_0017, g32p_row03_traceSegment_010_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2539 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2531 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2531 8 9, g32p_row03_traceSegment_010_2531_0008, g32p_row03_traceSegment_010_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2556 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2548 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2548 8 9, g32p_row03_traceSegment_010_2548_0008, g32p_row03_traceSegment_010_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2531 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2531 17 17, g32p_row03_traceSegment_010_2531_0017, g32p_row03_traceSegment_010_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 2497 68 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2497 34 34, g32p_row03_traceSegment_010_2497_0034, g32p_row03_traceSegment_010_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 2430 135 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2430 67 68, g32p_row03_traceSegment_010_2430_0067, g32p_row03_traceSegment_010_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 2565 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2581 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2581 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2581 8 9, g32p_row03_traceSegment_010_2581_0008, g32p_row03_traceSegment_010_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 2565 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2565 16 17, g32p_row03_traceSegment_010_2565_0016, g32p_row03_traceSegment_010_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2598 8 9, g32p_row03_traceSegment_010_2598_0008, g32p_row03_traceSegment_010_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2615 8 9, g32p_row03_traceSegment_010_2615_0008, g32p_row03_traceSegment_010_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2598 17 17, g32p_row03_traceSegment_010_2598_0017, g32p_row03_traceSegment_010_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 2565 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2565 33 34, g32p_row03_traceSegment_010_2565_0033, g32p_row03_traceSegment_010_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2632 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2632 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2632 8 9, g32p_row03_traceSegment_010_2632_0008, g32p_row03_traceSegment_010_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2657 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2649 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2649 8 9, g32p_row03_traceSegment_010_2649_0008, g32p_row03_traceSegment_010_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2632 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2632 17 17, g32p_row03_traceSegment_010_2632_0017, g32p_row03_traceSegment_010_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2674 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2666 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2666 8 9, g32p_row03_traceSegment_010_2666_0008, g32p_row03_traceSegment_010_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2683 8 9, g32p_row03_traceSegment_010_2683_0008, g32p_row03_traceSegment_010_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2666 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2666 17 17, g32p_row03_traceSegment_010_2666_0017, g32p_row03_traceSegment_010_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 2632 68 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2632 34 34, g32p_row03_traceSegment_010_2632_0034, g32p_row03_traceSegment_010_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 2565 135 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2565 67 68, g32p_row03_traceSegment_010_2565_0067, g32p_row03_traceSegment_010_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 2430 270 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2430 135 135, g32p_row03_traceSegment_010_2430_0135, g32p_row03_traceSegment_010_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_010 2160 540 = [0, 0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2160 270 270, g32p_row03_traceSegment_010_2160_0270, g32p_row03_traceSegment_010_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 2700 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2724 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2716 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2716 8 9, g32p_row03_traceSegment_010_2716_0008, g32p_row03_traceSegment_010_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 2700 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2700 16 17, g32p_row03_traceSegment_010_2700_0016, g32p_row03_traceSegment_010_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2733 8 9, g32p_row03_traceSegment_010_2733_0008, g32p_row03_traceSegment_010_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2758 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2750 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2750 8 9, g32p_row03_traceSegment_010_2750_0008, g32p_row03_traceSegment_010_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2733 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2733 17 17, g32p_row03_traceSegment_010_2733_0017, g32p_row03_traceSegment_010_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 2700 67 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2700 33 34, g32p_row03_traceSegment_010_2700_0033, g32p_row03_traceSegment_010_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2767 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2775 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2767 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2767 8 9, g32p_row03_traceSegment_010_2767_0008, g32p_row03_traceSegment_010_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2784 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2784 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2784 8 9, g32p_row03_traceSegment_010_2784_0008, g32p_row03_traceSegment_010_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2767 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2767 17 17, g32p_row03_traceSegment_010_2767_0017, g32p_row03_traceSegment_010_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2801 8 9, g32p_row03_traceSegment_010_2801_0008, g32p_row03_traceSegment_010_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2818 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2826 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2818 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2818 8 9, g32p_row03_traceSegment_010_2818_0008, g32p_row03_traceSegment_010_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2801 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2801 17 17, g32p_row03_traceSegment_010_2801_0017, g32p_row03_traceSegment_010_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 2767 68 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2767 34 34, g32p_row03_traceSegment_010_2767_0034, g32p_row03_traceSegment_010_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 2700 135 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2700 67 68, g32p_row03_traceSegment_010_2700_0067, g32p_row03_traceSegment_010_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 2835 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2851 8 9, g32p_row03_traceSegment_010_2851_0008, g32p_row03_traceSegment_010_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 2835 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2835 16 17, g32p_row03_traceSegment_010_2835_0016, g32p_row03_traceSegment_010_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2868 8 9, g32p_row03_traceSegment_010_2868_0008, g32p_row03_traceSegment_010_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2885 8 9, g32p_row03_traceSegment_010_2885_0008, g32p_row03_traceSegment_010_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2868 17 17, g32p_row03_traceSegment_010_2868_0017, g32p_row03_traceSegment_010_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 2835 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2835 33 34, g32p_row03_traceSegment_010_2835_0033, g32p_row03_traceSegment_010_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2910 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2902 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2902 8 9, g32p_row03_traceSegment_010_2902_0008, g32p_row03_traceSegment_010_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2927 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2919 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2919 8 9, g32p_row03_traceSegment_010_2919_0008, g32p_row03_traceSegment_010_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2902 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2902 17 17, g32p_row03_traceSegment_010_2902_0017, g32p_row03_traceSegment_010_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2936 8 9, g32p_row03_traceSegment_010_2936_0008, g32p_row03_traceSegment_010_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2953 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2953 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2953 8 9, g32p_row03_traceSegment_010_2953_0008, g32p_row03_traceSegment_010_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 2936 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2936 17 17, g32p_row03_traceSegment_010_2936_0017, g32p_row03_traceSegment_010_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 2902 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2902 34 34, g32p_row03_traceSegment_010_2902_0034, g32p_row03_traceSegment_010_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 2835 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2835 67 68, g32p_row03_traceSegment_010_2835_0067, g32p_row03_traceSegment_010_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 2700 270 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2700 135 135, g32p_row03_traceSegment_010_2700_0135, g32p_row03_traceSegment_010_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 2970 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2986 8 9, g32p_row03_traceSegment_010_2986_0008, g32p_row03_traceSegment_010_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 2970 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2970 16 17, g32p_row03_traceSegment_010_2970_0016, g32p_row03_traceSegment_010_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3003 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3003 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3003 8 9, g32p_row03_traceSegment_010_3003_0008, g32p_row03_traceSegment_010_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3020 8 9, g32p_row03_traceSegment_010_3020_0008, g32p_row03_traceSegment_010_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3003 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3003 17 17, g32p_row03_traceSegment_010_3003_0017, g32p_row03_traceSegment_010_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 2970 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2970 33 34, g32p_row03_traceSegment_010_2970_0033, g32p_row03_traceSegment_010_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3037 8 9, g32p_row03_traceSegment_010_3037_0008, g32p_row03_traceSegment_010_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3054 8 9, g32p_row03_traceSegment_010_3054_0008, g32p_row03_traceSegment_010_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3037 17 17, g32p_row03_traceSegment_010_3037_0017, g32p_row03_traceSegment_010_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3071 8 9, g32p_row03_traceSegment_010_3071_0008, g32p_row03_traceSegment_010_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3088 8 9, g32p_row03_traceSegment_010_3088_0008, g32p_row03_traceSegment_010_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3071 17 17, g32p_row03_traceSegment_010_3071_0017, g32p_row03_traceSegment_010_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3037 34 34, g32p_row03_traceSegment_010_3037_0034, g32p_row03_traceSegment_010_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 2970 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2970 67 68, g32p_row03_traceSegment_010_2970_0067, g32p_row03_traceSegment_010_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3121 8 9, g32p_row03_traceSegment_010_3121_0008, g32p_row03_traceSegment_010_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3105 16 17, g32p_row03_traceSegment_010_3105_0016, g32p_row03_traceSegment_010_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3138 8 9, g32p_row03_traceSegment_010_3138_0008, g32p_row03_traceSegment_010_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3155 8 9, g32p_row03_traceSegment_010_3155_0008, g32p_row03_traceSegment_010_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3138 17 17, g32p_row03_traceSegment_010_3138_0017, g32p_row03_traceSegment_010_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3105 33 34, g32p_row03_traceSegment_010_3105_0033, g32p_row03_traceSegment_010_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3172 8 9, g32p_row03_traceSegment_010_3172_0008, g32p_row03_traceSegment_010_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3189 8 9, g32p_row03_traceSegment_010_3189_0008, g32p_row03_traceSegment_010_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3172 17 17, g32p_row03_traceSegment_010_3172_0017, g32p_row03_traceSegment_010_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3206 8 9, g32p_row03_traceSegment_010_3206_0008, g32p_row03_traceSegment_010_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3223 8 9, g32p_row03_traceSegment_010_3223_0008, g32p_row03_traceSegment_010_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3206 17 17, g32p_row03_traceSegment_010_3206_0017, g32p_row03_traceSegment_010_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3172 34 34, g32p_row03_traceSegment_010_3172_0034, g32p_row03_traceSegment_010_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3105 67 68, g32p_row03_traceSegment_010_3105_0067, g32p_row03_traceSegment_010_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 2970 270 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2970 135 135, g32p_row03_traceSegment_010_2970_0135, g32p_row03_traceSegment_010_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_010 2700 540 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2700 270 270, g32p_row03_traceSegment_010_2700_0270, g32p_row03_traceSegment_010_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_010 2160 1080 = [0, 0, 0, 0, 0, 35] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2160 540 540, g32p_row03_traceSegment_010_2160_0540, g32p_row03_traceSegment_010_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3256 8 9, g32p_row03_traceSegment_010_3256_0008, g32p_row03_traceSegment_010_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3240 16 17, g32p_row03_traceSegment_010_3240_0016, g32p_row03_traceSegment_010_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3273 8 9, g32p_row03_traceSegment_010_3273_0008, g32p_row03_traceSegment_010_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3290 8 9, g32p_row03_traceSegment_010_3290_0008, g32p_row03_traceSegment_010_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3273 17 17, g32p_row03_traceSegment_010_3273_0017, g32p_row03_traceSegment_010_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3240 33 34, g32p_row03_traceSegment_010_3240_0033, g32p_row03_traceSegment_010_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3307 8 9, g32p_row03_traceSegment_010_3307_0008, g32p_row03_traceSegment_010_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3324 8 9, g32p_row03_traceSegment_010_3324_0008, g32p_row03_traceSegment_010_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3307 17 17, g32p_row03_traceSegment_010_3307_0017, g32p_row03_traceSegment_010_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3341 8 9, g32p_row03_traceSegment_010_3341_0008, g32p_row03_traceSegment_010_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3358 8 9, g32p_row03_traceSegment_010_3358_0008, g32p_row03_traceSegment_010_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3341 17 17, g32p_row03_traceSegment_010_3341_0017, g32p_row03_traceSegment_010_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3307 34 34, g32p_row03_traceSegment_010_3307_0034, g32p_row03_traceSegment_010_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3240 67 68, g32p_row03_traceSegment_010_3240_0067, g32p_row03_traceSegment_010_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3391 8 9, g32p_row03_traceSegment_010_3391_0008, g32p_row03_traceSegment_010_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3375 16 17, g32p_row03_traceSegment_010_3375_0016, g32p_row03_traceSegment_010_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3408 8 9, g32p_row03_traceSegment_010_3408_0008, g32p_row03_traceSegment_010_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3425 8 9, g32p_row03_traceSegment_010_3425_0008, g32p_row03_traceSegment_010_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3408 17 17, g32p_row03_traceSegment_010_3408_0017, g32p_row03_traceSegment_010_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3375 33 34, g32p_row03_traceSegment_010_3375_0033, g32p_row03_traceSegment_010_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3442 8 9, g32p_row03_traceSegment_010_3442_0008, g32p_row03_traceSegment_010_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3459 8 9, g32p_row03_traceSegment_010_3459_0008, g32p_row03_traceSegment_010_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3442 17 17, g32p_row03_traceSegment_010_3442_0017, g32p_row03_traceSegment_010_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3476 8 9, g32p_row03_traceSegment_010_3476_0008, g32p_row03_traceSegment_010_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3493 8 9, g32p_row03_traceSegment_010_3493_0008, g32p_row03_traceSegment_010_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3476 17 17, g32p_row03_traceSegment_010_3476_0017, g32p_row03_traceSegment_010_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3442 34 34, g32p_row03_traceSegment_010_3442_0034, g32p_row03_traceSegment_010_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3375 67 68, g32p_row03_traceSegment_010_3375_0067, g32p_row03_traceSegment_010_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3240 135 135, g32p_row03_traceSegment_010_3240_0135, g32p_row03_traceSegment_010_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3526 8 9, g32p_row03_traceSegment_010_3526_0008, g32p_row03_traceSegment_010_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3510 16 17, g32p_row03_traceSegment_010_3510_0016, g32p_row03_traceSegment_010_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3543 8 9, g32p_row03_traceSegment_010_3543_0008, g32p_row03_traceSegment_010_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3560 8 9, g32p_row03_traceSegment_010_3560_0008, g32p_row03_traceSegment_010_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3543 17 17, g32p_row03_traceSegment_010_3543_0017, g32p_row03_traceSegment_010_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3510 33 34, g32p_row03_traceSegment_010_3510_0033, g32p_row03_traceSegment_010_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3577 8 9, g32p_row03_traceSegment_010_3577_0008, g32p_row03_traceSegment_010_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3594 8 9, g32p_row03_traceSegment_010_3594_0008, g32p_row03_traceSegment_010_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3577 17 17, g32p_row03_traceSegment_010_3577_0017, g32p_row03_traceSegment_010_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3611 8 9, g32p_row03_traceSegment_010_3611_0008, g32p_row03_traceSegment_010_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3628 8 9, g32p_row03_traceSegment_010_3628_0008, g32p_row03_traceSegment_010_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3611 17 17, g32p_row03_traceSegment_010_3611_0017, g32p_row03_traceSegment_010_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3577 34 34, g32p_row03_traceSegment_010_3577_0034, g32p_row03_traceSegment_010_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3510 67 68, g32p_row03_traceSegment_010_3510_0067, g32p_row03_traceSegment_010_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3661 8 9, g32p_row03_traceSegment_010_3661_0008, g32p_row03_traceSegment_010_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3645 16 17, g32p_row03_traceSegment_010_3645_0016, g32p_row03_traceSegment_010_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3678 8 9, g32p_row03_traceSegment_010_3678_0008, g32p_row03_traceSegment_010_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3695 8 9, g32p_row03_traceSegment_010_3695_0008, g32p_row03_traceSegment_010_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3678 17 17, g32p_row03_traceSegment_010_3678_0017, g32p_row03_traceSegment_010_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3645 33 34, g32p_row03_traceSegment_010_3645_0033, g32p_row03_traceSegment_010_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3712 8 9, g32p_row03_traceSegment_010_3712_0008, g32p_row03_traceSegment_010_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3729 8 9, g32p_row03_traceSegment_010_3729_0008, g32p_row03_traceSegment_010_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3712 17 17, g32p_row03_traceSegment_010_3712_0017, g32p_row03_traceSegment_010_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3746 8 9, g32p_row03_traceSegment_010_3746_0008, g32p_row03_traceSegment_010_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3763 8 9, g32p_row03_traceSegment_010_3763_0008, g32p_row03_traceSegment_010_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3746 17 17, g32p_row03_traceSegment_010_3746_0017, g32p_row03_traceSegment_010_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3712 34 34, g32p_row03_traceSegment_010_3712_0034, g32p_row03_traceSegment_010_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3645 67 68, g32p_row03_traceSegment_010_3645_0067, g32p_row03_traceSegment_010_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 3510 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3510 135 135, g32p_row03_traceSegment_010_3510_0135, g32p_row03_traceSegment_010_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_010 3240 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3240 270 270, g32p_row03_traceSegment_010_3240_0270, g32p_row03_traceSegment_010_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3796 8 9, g32p_row03_traceSegment_010_3796_0008, g32p_row03_traceSegment_010_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3780 16 17, g32p_row03_traceSegment_010_3780_0016, g32p_row03_traceSegment_010_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3821 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3813 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3813 8 9, g32p_row03_traceSegment_010_3813_0008, g32p_row03_traceSegment_010_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3830 8 9, g32p_row03_traceSegment_010_3830_0008, g32p_row03_traceSegment_010_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3813 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3813 17 17, g32p_row03_traceSegment_010_3813_0017, g32p_row03_traceSegment_010_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 3780 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3780 33 34, g32p_row03_traceSegment_010_3780_0033, g32p_row03_traceSegment_010_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3847 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3847 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3847 8 9, g32p_row03_traceSegment_010_3847_0008, g32p_row03_traceSegment_010_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3864 8 9, g32p_row03_traceSegment_010_3864_0008, g32p_row03_traceSegment_010_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3847 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3847 17 17, g32p_row03_traceSegment_010_3847_0017, g32p_row03_traceSegment_010_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3881 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3881 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3881 8 9, g32p_row03_traceSegment_010_3881_0008, g32p_row03_traceSegment_010_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3898 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3898 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3898 8 9, g32p_row03_traceSegment_010_3898_0008, g32p_row03_traceSegment_010_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3881 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3881 17 17, g32p_row03_traceSegment_010_3881_0017, g32p_row03_traceSegment_010_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 3847 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3847 34 34, g32p_row03_traceSegment_010_3847_0034, g32p_row03_traceSegment_010_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 3780 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3780 67 68, g32p_row03_traceSegment_010_3780_0067, g32p_row03_traceSegment_010_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3939 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3931 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3931 8 9, g32p_row03_traceSegment_010_3931_0008, g32p_row03_traceSegment_010_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 3915 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3915 16 17, g32p_row03_traceSegment_010_3915_0016, g32p_row03_traceSegment_010_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3948 8 9, g32p_row03_traceSegment_010_3948_0008, g32p_row03_traceSegment_010_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3973 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3965 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3965 8 9, g32p_row03_traceSegment_010_3965_0008, g32p_row03_traceSegment_010_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3948 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3948 17 17, g32p_row03_traceSegment_010_3948_0017, g32p_row03_traceSegment_010_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 3915 67 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3915 33 34, g32p_row03_traceSegment_010_3915_0033, g32p_row03_traceSegment_010_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3982 8 9, g32p_row03_traceSegment_010_3982_0008, g32p_row03_traceSegment_010_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 3999 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4007 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 3999 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3999 8 9, g32p_row03_traceSegment_010_3999_0008, g32p_row03_traceSegment_010_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 3982 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3982 17 17, g32p_row03_traceSegment_010_3982_0017, g32p_row03_traceSegment_010_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4016 8 9, g32p_row03_traceSegment_010_4016_0008, g32p_row03_traceSegment_010_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4041 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4033 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4033 8 9, g32p_row03_traceSegment_010_4033_0008, g32p_row03_traceSegment_010_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 4016 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4016 17 17, g32p_row03_traceSegment_010_4016_0017, g32p_row03_traceSegment_010_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 3982 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3982 34 34, g32p_row03_traceSegment_010_3982_0034, g32p_row03_traceSegment_010_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 3915 135 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3915 67 68, g32p_row03_traceSegment_010_3915_0067, g32p_row03_traceSegment_010_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 3780 270 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3780 135 135, g32p_row03_traceSegment_010_3780_0135, g32p_row03_traceSegment_010_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 4050 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4066 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4066 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4066 8 9, g32p_row03_traceSegment_010_4066_0008, g32p_row03_traceSegment_010_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 4050 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4050 16 17, g32p_row03_traceSegment_010_4050_0016, g32p_row03_traceSegment_010_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4083 8 9, g32p_row03_traceSegment_010_4083_0008, g32p_row03_traceSegment_010_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4108 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4100 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4100 8 9, g32p_row03_traceSegment_010_4100_0008, g32p_row03_traceSegment_010_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 4083 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4083 17 17, g32p_row03_traceSegment_010_4083_0017, g32p_row03_traceSegment_010_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 4050 67 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4050 33 34, g32p_row03_traceSegment_010_4050_0033, g32p_row03_traceSegment_010_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4117 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4125 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4117 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4117 8 9, g32p_row03_traceSegment_010_4117_0008, g32p_row03_traceSegment_010_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4134 8 9, g32p_row03_traceSegment_010_4134_0008, g32p_row03_traceSegment_010_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 4117 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4117 17 17, g32p_row03_traceSegment_010_4117_0017, g32p_row03_traceSegment_010_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4151 8 9, g32p_row03_traceSegment_010_4151_0008, g32p_row03_traceSegment_010_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4168 8 9, g32p_row03_traceSegment_010_4168_0008, g32p_row03_traceSegment_010_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4151 17 17, g32p_row03_traceSegment_010_4151_0017, g32p_row03_traceSegment_010_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 4117 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4117 34 34, g32p_row03_traceSegment_010_4117_0034, g32p_row03_traceSegment_010_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 4050 135 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4050 67 68, g32p_row03_traceSegment_010_4050_0067, g32p_row03_traceSegment_010_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_010 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4201 8 9, g32p_row03_traceSegment_010_4201_0008, g32p_row03_traceSegment_010_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_010 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4185 16 17, g32p_row03_traceSegment_010_4185_0016, g32p_row03_traceSegment_010_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4218 8 9, g32p_row03_traceSegment_010_4218_0008, g32p_row03_traceSegment_010_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4235 8 9, g32p_row03_traceSegment_010_4235_0008, g32p_row03_traceSegment_010_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4218 17 17, g32p_row03_traceSegment_010_4218_0017, g32p_row03_traceSegment_010_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_010 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4185 33 34, g32p_row03_traceSegment_010_4185_0033, g32p_row03_traceSegment_010_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4252 8 9, g32p_row03_traceSegment_010_4252_0008, g32p_row03_traceSegment_010_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4269 8 9, g32p_row03_traceSegment_010_4269_0008, g32p_row03_traceSegment_010_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4252 17 17, g32p_row03_traceSegment_010_4252_0017, g32p_row03_traceSegment_010_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4286 8 9, g32p_row03_traceSegment_010_4286_0008, g32p_row03_traceSegment_010_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_010 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_010 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_010_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_010 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4303 8 9, g32p_row03_traceSegment_010_4303_0008, g32p_row03_traceSegment_010_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_010 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4286 17 17, g32p_row03_traceSegment_010_4286_0017, g32p_row03_traceSegment_010_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_010 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4252 34 34, g32p_row03_traceSegment_010_4252_0034, g32p_row03_traceSegment_010_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_010 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4185 67 68, g32p_row03_traceSegment_010_4185_0067, g32p_row03_traceSegment_010_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_010_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_010 4050 270 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 4050 135 135, g32p_row03_traceSegment_010_4050_0135, g32p_row03_traceSegment_010_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_010 3780 540 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3780 270 270, g32p_row03_traceSegment_010_3780_0270, g32p_row03_traceSegment_010_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_010_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_010 3240 1080 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 3240 540 540, g32p_row03_traceSegment_010_3240_0540, g32p_row03_traceSegment_010_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_010_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_010 2160 2160 = [0, 0, 0, 0, 0, 50] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 2160 1080 1080, g32p_row03_traceSegment_010_2160_1080, g32p_row03_traceSegment_010_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_010_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_010 0 4320 = [0, 0, 0, 0, 0, 120] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_010 0 2160 2160, g32p_row03_traceSegment_010_0000_2160, g32p_row03_traceSegment_010_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 10 = [0, 0, 0, 0, 0, 120] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_010_0000_4320

end HodgeLean.Foundations.Program

end
end
