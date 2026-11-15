import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0328
import HodgeLean.Foundations.Program.G32PropFourSixPacked0327
import HodgeLean.Foundations.Program.G32PropFourSixPacked0326

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_071 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 71 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_071_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 16 8 9, g32p_row03_traceSegment_071_0016_0008, g32p_row03_traceSegment_071_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 0 16 17, g32p_row03_traceSegment_071_0000_0016, g32p_row03_traceSegment_071_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 33 8 9, g32p_row03_traceSegment_071_0033_0008, g32p_row03_traceSegment_071_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 50 8 9, g32p_row03_traceSegment_071_0050_0008, g32p_row03_traceSegment_071_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 33 17 17, g32p_row03_traceSegment_071_0033_0017, g32p_row03_traceSegment_071_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 0 33 34, g32p_row03_traceSegment_071_0000_0033, g32p_row03_traceSegment_071_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 67 8 9, g32p_row03_traceSegment_071_0067_0008, g32p_row03_traceSegment_071_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 84 8 9, g32p_row03_traceSegment_071_0084_0008, g32p_row03_traceSegment_071_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 67 17 17, g32p_row03_traceSegment_071_0067_0017, g32p_row03_traceSegment_071_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 101 8 9, g32p_row03_traceSegment_071_0101_0008, g32p_row03_traceSegment_071_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 118 8 9, g32p_row03_traceSegment_071_0118_0008, g32p_row03_traceSegment_071_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 101 17 17, g32p_row03_traceSegment_071_0101_0017, g32p_row03_traceSegment_071_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 67 34 34, g32p_row03_traceSegment_071_0067_0034, g32p_row03_traceSegment_071_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 0 67 68, g32p_row03_traceSegment_071_0000_0067, g32p_row03_traceSegment_071_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 151 8 9, g32p_row03_traceSegment_071_0151_0008, g32p_row03_traceSegment_071_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 135 16 17, g32p_row03_traceSegment_071_0135_0016, g32p_row03_traceSegment_071_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 168 8 9, g32p_row03_traceSegment_071_0168_0008, g32p_row03_traceSegment_071_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 185 8 9, g32p_row03_traceSegment_071_0185_0008, g32p_row03_traceSegment_071_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 168 17 17, g32p_row03_traceSegment_071_0168_0017, g32p_row03_traceSegment_071_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 135 33 34, g32p_row03_traceSegment_071_0135_0033, g32p_row03_traceSegment_071_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 202 8 9, g32p_row03_traceSegment_071_0202_0008, g32p_row03_traceSegment_071_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 219 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 227 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 219 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 219 8 9, g32p_row03_traceSegment_071_0219_0008, g32p_row03_traceSegment_071_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 202 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 202 17 17, g32p_row03_traceSegment_071_0202_0017, g32p_row03_traceSegment_071_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 236 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 244 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 236 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 236 8 9, g32p_row03_traceSegment_071_0236_0008, g32p_row03_traceSegment_071_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 253 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 261 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 253 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 253 8 9, g32p_row03_traceSegment_071_0253_0008, g32p_row03_traceSegment_071_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 236 34 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 236 17 17, g32p_row03_traceSegment_071_0236_0017, g32p_row03_traceSegment_071_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 202 68 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 202 34 34, g32p_row03_traceSegment_071_0202_0034, g32p_row03_traceSegment_071_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 135 135 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 135 67 68, g32p_row03_traceSegment_071_0135_0067, g32p_row03_traceSegment_071_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 0 270 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 0 135 135, g32p_row03_traceSegment_071_0000_0135, g32p_row03_traceSegment_071_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 270 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 286 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 294 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 286 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 286 8 9, g32p_row03_traceSegment_071_0286_0008, g32p_row03_traceSegment_071_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 270 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 270 16 17, g32p_row03_traceSegment_071_0270_0016, g32p_row03_traceSegment_071_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 303 8 9, g32p_row03_traceSegment_071_0303_0008, g32p_row03_traceSegment_071_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 320 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 320 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 320 8 9, g32p_row03_traceSegment_071_0320_0008, g32p_row03_traceSegment_071_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 303 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 303 17 17, g32p_row03_traceSegment_071_0303_0017, g32p_row03_traceSegment_071_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 270 67 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 270 33 34, g32p_row03_traceSegment_071_0270_0033, g32p_row03_traceSegment_071_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 337 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 337 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 337 8 9, g32p_row03_traceSegment_071_0337_0008, g32p_row03_traceSegment_071_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 354 8 9, g32p_row03_traceSegment_071_0354_0008, g32p_row03_traceSegment_071_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 337 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 337 17 17, g32p_row03_traceSegment_071_0337_0017, g32p_row03_traceSegment_071_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 371 8 9, g32p_row03_traceSegment_071_0371_0008, g32p_row03_traceSegment_071_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 388 8 9, g32p_row03_traceSegment_071_0388_0008, g32p_row03_traceSegment_071_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 371 17 17, g32p_row03_traceSegment_071_0371_0017, g32p_row03_traceSegment_071_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 337 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 337 34 34, g32p_row03_traceSegment_071_0337_0034, g32p_row03_traceSegment_071_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 270 135 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 270 67 68, g32p_row03_traceSegment_071_0270_0067, g32p_row03_traceSegment_071_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 421 8 9, g32p_row03_traceSegment_071_0421_0008, g32p_row03_traceSegment_071_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 405 16 17, g32p_row03_traceSegment_071_0405_0016, g32p_row03_traceSegment_071_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 438 8 9, g32p_row03_traceSegment_071_0438_0008, g32p_row03_traceSegment_071_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 455 8 9, g32p_row03_traceSegment_071_0455_0008, g32p_row03_traceSegment_071_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 438 17 17, g32p_row03_traceSegment_071_0438_0017, g32p_row03_traceSegment_071_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 405 33 34, g32p_row03_traceSegment_071_0405_0033, g32p_row03_traceSegment_071_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 472 8 9, g32p_row03_traceSegment_071_0472_0008, g32p_row03_traceSegment_071_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 489 8 9, g32p_row03_traceSegment_071_0489_0008, g32p_row03_traceSegment_071_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 472 17 17, g32p_row03_traceSegment_071_0472_0017, g32p_row03_traceSegment_071_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 506 8 9, g32p_row03_traceSegment_071_0506_0008, g32p_row03_traceSegment_071_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 523 8 9, g32p_row03_traceSegment_071_0523_0008, g32p_row03_traceSegment_071_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 506 17 17, g32p_row03_traceSegment_071_0506_0017, g32p_row03_traceSegment_071_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 472 34 34, g32p_row03_traceSegment_071_0472_0034, g32p_row03_traceSegment_071_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 405 67 68, g32p_row03_traceSegment_071_0405_0067, g32p_row03_traceSegment_071_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 270 270 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 270 135 135, g32p_row03_traceSegment_071_0270_0135, g32p_row03_traceSegment_071_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_071 0 540 = [0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 0 270 270, g32p_row03_traceSegment_071_0000_0270, g32p_row03_traceSegment_071_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 556 8 9, g32p_row03_traceSegment_071_0556_0008, g32p_row03_traceSegment_071_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 540 16 17, g32p_row03_traceSegment_071_0540_0016, g32p_row03_traceSegment_071_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 573 8 9, g32p_row03_traceSegment_071_0573_0008, g32p_row03_traceSegment_071_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 590 8 9, g32p_row03_traceSegment_071_0590_0008, g32p_row03_traceSegment_071_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 573 17 17, g32p_row03_traceSegment_071_0573_0017, g32p_row03_traceSegment_071_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 540 33 34, g32p_row03_traceSegment_071_0540_0033, g32p_row03_traceSegment_071_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 607 8 9, g32p_row03_traceSegment_071_0607_0008, g32p_row03_traceSegment_071_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 624 8 9, g32p_row03_traceSegment_071_0624_0008, g32p_row03_traceSegment_071_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 607 17 17, g32p_row03_traceSegment_071_0607_0017, g32p_row03_traceSegment_071_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 641 8 9, g32p_row03_traceSegment_071_0641_0008, g32p_row03_traceSegment_071_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 658 8 9, g32p_row03_traceSegment_071_0658_0008, g32p_row03_traceSegment_071_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 641 17 17, g32p_row03_traceSegment_071_0641_0017, g32p_row03_traceSegment_071_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 607 34 34, g32p_row03_traceSegment_071_0607_0034, g32p_row03_traceSegment_071_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 540 67 68, g32p_row03_traceSegment_071_0540_0067, g32p_row03_traceSegment_071_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 691 8 9, g32p_row03_traceSegment_071_0691_0008, g32p_row03_traceSegment_071_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 675 16 17, g32p_row03_traceSegment_071_0675_0016, g32p_row03_traceSegment_071_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 708 8 9, g32p_row03_traceSegment_071_0708_0008, g32p_row03_traceSegment_071_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 725 8 9, g32p_row03_traceSegment_071_0725_0008, g32p_row03_traceSegment_071_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 708 17 17, g32p_row03_traceSegment_071_0708_0017, g32p_row03_traceSegment_071_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 675 33 34, g32p_row03_traceSegment_071_0675_0033, g32p_row03_traceSegment_071_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 742 8 9, g32p_row03_traceSegment_071_0742_0008, g32p_row03_traceSegment_071_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 759 8 9, g32p_row03_traceSegment_071_0759_0008, g32p_row03_traceSegment_071_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 742 17 17, g32p_row03_traceSegment_071_0742_0017, g32p_row03_traceSegment_071_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 776 8 9, g32p_row03_traceSegment_071_0776_0008, g32p_row03_traceSegment_071_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 793 8 9, g32p_row03_traceSegment_071_0793_0008, g32p_row03_traceSegment_071_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 776 17 17, g32p_row03_traceSegment_071_0776_0017, g32p_row03_traceSegment_071_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 742 34 34, g32p_row03_traceSegment_071_0742_0034, g32p_row03_traceSegment_071_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 675 67 68, g32p_row03_traceSegment_071_0675_0067, g32p_row03_traceSegment_071_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 540 135 135, g32p_row03_traceSegment_071_0540_0135, g32p_row03_traceSegment_071_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 826 8 9, g32p_row03_traceSegment_071_0826_0008, g32p_row03_traceSegment_071_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 810 16 17, g32p_row03_traceSegment_071_0810_0016, g32p_row03_traceSegment_071_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 843 8 9, g32p_row03_traceSegment_071_0843_0008, g32p_row03_traceSegment_071_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 860 8 9, g32p_row03_traceSegment_071_0860_0008, g32p_row03_traceSegment_071_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 843 17 17, g32p_row03_traceSegment_071_0843_0017, g32p_row03_traceSegment_071_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 810 33 34, g32p_row03_traceSegment_071_0810_0033, g32p_row03_traceSegment_071_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 877 8 9, g32p_row03_traceSegment_071_0877_0008, g32p_row03_traceSegment_071_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 894 8 9, g32p_row03_traceSegment_071_0894_0008, g32p_row03_traceSegment_071_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 877 17 17, g32p_row03_traceSegment_071_0877_0017, g32p_row03_traceSegment_071_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 911 8 9, g32p_row03_traceSegment_071_0911_0008, g32p_row03_traceSegment_071_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 928 8 9, g32p_row03_traceSegment_071_0928_0008, g32p_row03_traceSegment_071_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 911 17 17, g32p_row03_traceSegment_071_0911_0017, g32p_row03_traceSegment_071_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 877 34 34, g32p_row03_traceSegment_071_0877_0034, g32p_row03_traceSegment_071_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 810 67 68, g32p_row03_traceSegment_071_0810_0067, g32p_row03_traceSegment_071_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 961 8 9, g32p_row03_traceSegment_071_0961_0008, g32p_row03_traceSegment_071_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 945 16 17, g32p_row03_traceSegment_071_0945_0016, g32p_row03_traceSegment_071_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 978 8 9, g32p_row03_traceSegment_071_0978_0008, g32p_row03_traceSegment_071_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 995 8 9, g32p_row03_traceSegment_071_0995_0008, g32p_row03_traceSegment_071_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 978 17 17, g32p_row03_traceSegment_071_0978_0017, g32p_row03_traceSegment_071_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 945 33 34, g32p_row03_traceSegment_071_0945_0033, g32p_row03_traceSegment_071_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1012 8 9, g32p_row03_traceSegment_071_1012_0008, g32p_row03_traceSegment_071_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1029 8 9, g32p_row03_traceSegment_071_1029_0008, g32p_row03_traceSegment_071_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1012 17 17, g32p_row03_traceSegment_071_1012_0017, g32p_row03_traceSegment_071_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1046 8 9, g32p_row03_traceSegment_071_1046_0008, g32p_row03_traceSegment_071_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1063 8 9, g32p_row03_traceSegment_071_1063_0008, g32p_row03_traceSegment_071_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1046 17 17, g32p_row03_traceSegment_071_1046_0017, g32p_row03_traceSegment_071_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1012 34 34, g32p_row03_traceSegment_071_1012_0034, g32p_row03_traceSegment_071_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 945 67 68, g32p_row03_traceSegment_071_0945_0067, g32p_row03_traceSegment_071_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 810 135 135, g32p_row03_traceSegment_071_0810_0135, g32p_row03_traceSegment_071_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_071 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 540 270 270, g32p_row03_traceSegment_071_0540_0270, g32p_row03_traceSegment_071_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_071 0 1080 = [0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 0 540 540, g32p_row03_traceSegment_071_0000_0540, g32p_row03_traceSegment_071_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1096 8 9, g32p_row03_traceSegment_071_1096_0008, g32p_row03_traceSegment_071_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1080 16 17, g32p_row03_traceSegment_071_1080_0016, g32p_row03_traceSegment_071_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1113 8 9, g32p_row03_traceSegment_071_1113_0008, g32p_row03_traceSegment_071_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1130 8 9, g32p_row03_traceSegment_071_1130_0008, g32p_row03_traceSegment_071_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1113 17 17, g32p_row03_traceSegment_071_1113_0017, g32p_row03_traceSegment_071_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1080 33 34, g32p_row03_traceSegment_071_1080_0033, g32p_row03_traceSegment_071_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1147 8 9, g32p_row03_traceSegment_071_1147_0008, g32p_row03_traceSegment_071_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1164 8 9, g32p_row03_traceSegment_071_1164_0008, g32p_row03_traceSegment_071_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1147 17 17, g32p_row03_traceSegment_071_1147_0017, g32p_row03_traceSegment_071_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1181 8 9, g32p_row03_traceSegment_071_1181_0008, g32p_row03_traceSegment_071_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1198 8 9, g32p_row03_traceSegment_071_1198_0008, g32p_row03_traceSegment_071_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1181 17 17, g32p_row03_traceSegment_071_1181_0017, g32p_row03_traceSegment_071_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1147 34 34, g32p_row03_traceSegment_071_1147_0034, g32p_row03_traceSegment_071_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1080 67 68, g32p_row03_traceSegment_071_1080_0067, g32p_row03_traceSegment_071_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1231 8 9, g32p_row03_traceSegment_071_1231_0008, g32p_row03_traceSegment_071_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1215 16 17, g32p_row03_traceSegment_071_1215_0016, g32p_row03_traceSegment_071_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1248 8 9, g32p_row03_traceSegment_071_1248_0008, g32p_row03_traceSegment_071_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1265 8 9, g32p_row03_traceSegment_071_1265_0008, g32p_row03_traceSegment_071_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1248 17 17, g32p_row03_traceSegment_071_1248_0017, g32p_row03_traceSegment_071_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1215 33 34, g32p_row03_traceSegment_071_1215_0033, g32p_row03_traceSegment_071_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1282 8 9, g32p_row03_traceSegment_071_1282_0008, g32p_row03_traceSegment_071_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1299 8 9, g32p_row03_traceSegment_071_1299_0008, g32p_row03_traceSegment_071_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1282 17 17, g32p_row03_traceSegment_071_1282_0017, g32p_row03_traceSegment_071_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1316 8 9, g32p_row03_traceSegment_071_1316_0008, g32p_row03_traceSegment_071_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1341 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1333 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1333 8 9, g32p_row03_traceSegment_071_1333_0008, g32p_row03_traceSegment_071_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1316 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1316 17 17, g32p_row03_traceSegment_071_1316_0017, g32p_row03_traceSegment_071_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 1282 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1282 34 34, g32p_row03_traceSegment_071_1282_0034, g32p_row03_traceSegment_071_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 1215 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1215 67 68, g32p_row03_traceSegment_071_1215_0067, g32p_row03_traceSegment_071_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 1080 270 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1080 135 135, g32p_row03_traceSegment_071_1080_0135, g32p_row03_traceSegment_071_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1366 8 9, g32p_row03_traceSegment_071_1366_0008, g32p_row03_traceSegment_071_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1350 16 17, g32p_row03_traceSegment_071_1350_0016, g32p_row03_traceSegment_071_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1391 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1383 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1383 8 9, g32p_row03_traceSegment_071_1383_0008, g32p_row03_traceSegment_071_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1400 8 9, g32p_row03_traceSegment_071_1400_0008, g32p_row03_traceSegment_071_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1383 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1383 17 17, g32p_row03_traceSegment_071_1383_0017, g32p_row03_traceSegment_071_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 1350 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1350 33 34, g32p_row03_traceSegment_071_1350_0033, g32p_row03_traceSegment_071_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1425 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1417 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1417 8 9, g32p_row03_traceSegment_071_1417_0008, g32p_row03_traceSegment_071_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1442 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1434 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1434 8 9, g32p_row03_traceSegment_071_1434_0008, g32p_row03_traceSegment_071_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1417 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1417 17 17, g32p_row03_traceSegment_071_1417_0017, g32p_row03_traceSegment_071_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1451 8 9, g32p_row03_traceSegment_071_1451_0008, g32p_row03_traceSegment_071_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1476 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1468 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1468 8 9, g32p_row03_traceSegment_071_1468_0008, g32p_row03_traceSegment_071_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1451 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1451 17 17, g32p_row03_traceSegment_071_1451_0017, g32p_row03_traceSegment_071_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 1417 68 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1417 34 34, g32p_row03_traceSegment_071_1417_0034, g32p_row03_traceSegment_071_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 1350 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1350 67 68, g32p_row03_traceSegment_071_1350_0067, g32p_row03_traceSegment_071_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1501 8 9, g32p_row03_traceSegment_071_1501_0008, g32p_row03_traceSegment_071_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1485 16 17, g32p_row03_traceSegment_071_1485_0016, g32p_row03_traceSegment_071_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1518 8 9, g32p_row03_traceSegment_071_1518_0008, g32p_row03_traceSegment_071_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1535 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1535 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1535 8 9, g32p_row03_traceSegment_071_1535_0008, g32p_row03_traceSegment_071_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1518 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1518 17 17, g32p_row03_traceSegment_071_1518_0017, g32p_row03_traceSegment_071_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 1485 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1485 33 34, g32p_row03_traceSegment_071_1485_0033, g32p_row03_traceSegment_071_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1552 8 9, g32p_row03_traceSegment_071_1552_0008, g32p_row03_traceSegment_071_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1569 8 9, g32p_row03_traceSegment_071_1569_0008, g32p_row03_traceSegment_071_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1552 17 17, g32p_row03_traceSegment_071_1552_0017, g32p_row03_traceSegment_071_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1586 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1594 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1586 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1586 8 9, g32p_row03_traceSegment_071_1586_0008, g32p_row03_traceSegment_071_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1611 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1603 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1603 8 9, g32p_row03_traceSegment_071_1603_0008, g32p_row03_traceSegment_071_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1586 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1586 17 17, g32p_row03_traceSegment_071_1586_0017, g32p_row03_traceSegment_071_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 1552 68 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1552 34 34, g32p_row03_traceSegment_071_1552_0034, g32p_row03_traceSegment_071_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 1485 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1485 67 68, g32p_row03_traceSegment_071_1485_0067, g32p_row03_traceSegment_071_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 1350 270 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1350 135 135, g32p_row03_traceSegment_071_1350_0135, g32p_row03_traceSegment_071_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_071 1080 540 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1080 270 270, g32p_row03_traceSegment_071_1080_0270, g32p_row03_traceSegment_071_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 1620 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1636 8 9, g32p_row03_traceSegment_071_1636_0008, g32p_row03_traceSegment_071_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 1620 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1620 16 17, g32p_row03_traceSegment_071_1620_0016, g32p_row03_traceSegment_071_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1661 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1653 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1653 8 9, g32p_row03_traceSegment_071_1653_0008, g32p_row03_traceSegment_071_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1670 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1670 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1670 8 9, g32p_row03_traceSegment_071_1670_0008, g32p_row03_traceSegment_071_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1653 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1653 17 17, g32p_row03_traceSegment_071_1653_0017, g32p_row03_traceSegment_071_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 1620 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1620 33 34, g32p_row03_traceSegment_071_1620_0033, g32p_row03_traceSegment_071_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1695 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1687 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1687 8 9, g32p_row03_traceSegment_071_1687_0008, g32p_row03_traceSegment_071_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1704 8 9, g32p_row03_traceSegment_071_1704_0008, g32p_row03_traceSegment_071_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1687 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1687 17 17, g32p_row03_traceSegment_071_1687_0017, g32p_row03_traceSegment_071_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1721 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1729 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1721 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1721 8 9, g32p_row03_traceSegment_071_1721_0008, g32p_row03_traceSegment_071_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1746 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1738 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1738 8 9, g32p_row03_traceSegment_071_1738_0008, g32p_row03_traceSegment_071_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1721 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1721 17 17, g32p_row03_traceSegment_071_1721_0017, g32p_row03_traceSegment_071_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 1687 68 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1687 34 34, g32p_row03_traceSegment_071_1687_0034, g32p_row03_traceSegment_071_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 1620 135 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1620 67 68, g32p_row03_traceSegment_071_1620_0067, g32p_row03_traceSegment_071_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 1755 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1771 8 9, g32p_row03_traceSegment_071_1771_0008, g32p_row03_traceSegment_071_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 1755 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1755 16 17, g32p_row03_traceSegment_071_1755_0016, g32p_row03_traceSegment_071_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1788 8 9, g32p_row03_traceSegment_071_1788_0008, g32p_row03_traceSegment_071_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1813 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1805 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1805 8 9, g32p_row03_traceSegment_071_1805_0008, g32p_row03_traceSegment_071_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1788 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1788 17 17, g32p_row03_traceSegment_071_1788_0017, g32p_row03_traceSegment_071_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 1755 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1755 33 34, g32p_row03_traceSegment_071_1755_0033, g32p_row03_traceSegment_071_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1822 8 9, g32p_row03_traceSegment_071_1822_0008, g32p_row03_traceSegment_071_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1847 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1839 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1839 8 9, g32p_row03_traceSegment_071_1839_0008, g32p_row03_traceSegment_071_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1822 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1822 17 17, g32p_row03_traceSegment_071_1822_0017, g32p_row03_traceSegment_071_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1856 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1864 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1856 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1856 8 9, g32p_row03_traceSegment_071_1856_0008, g32p_row03_traceSegment_071_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1881 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1873 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1873 8 9, g32p_row03_traceSegment_071_1873_0008, g32p_row03_traceSegment_071_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1856 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1856 17 17, g32p_row03_traceSegment_071_1856_0017, g32p_row03_traceSegment_071_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 1822 68 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1822 34 34, g32p_row03_traceSegment_071_1822_0034, g32p_row03_traceSegment_071_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 1755 135 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1755 67 68, g32p_row03_traceSegment_071_1755_0067, g32p_row03_traceSegment_071_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 1620 270 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1620 135 135, g32p_row03_traceSegment_071_1620_0135, g32p_row03_traceSegment_071_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 1890 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1906 8 9, g32p_row03_traceSegment_071_1906_0008, g32p_row03_traceSegment_071_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 1890 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1890 16 17, g32p_row03_traceSegment_071_1890_0016, g32p_row03_traceSegment_071_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1931 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1923 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1923 8 9, g32p_row03_traceSegment_071_1923_0008, g32p_row03_traceSegment_071_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1940 8 9, g32p_row03_traceSegment_071_1940_0008, g32p_row03_traceSegment_071_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1923 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1923 17 17, g32p_row03_traceSegment_071_1923_0017, g32p_row03_traceSegment_071_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 1890 67 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1890 33 34, g32p_row03_traceSegment_071_1890_0033, g32p_row03_traceSegment_071_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1965 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1957 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1957 8 9, g32p_row03_traceSegment_071_1957_0008, g32p_row03_traceSegment_071_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1974 8 9, g32p_row03_traceSegment_071_1974_0008, g32p_row03_traceSegment_071_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1957 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1957 17 17, g32p_row03_traceSegment_071_1957_0017, g32p_row03_traceSegment_071_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 1991 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 1991 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1991 8 9, g32p_row03_traceSegment_071_1991_0008, g32p_row03_traceSegment_071_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2008 8 9, g32p_row03_traceSegment_071_2008_0008, g32p_row03_traceSegment_071_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 1991 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1991 17 17, g32p_row03_traceSegment_071_1991_0017, g32p_row03_traceSegment_071_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 1957 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1957 34 34, g32p_row03_traceSegment_071_1957_0034, g32p_row03_traceSegment_071_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 1890 135 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1890 67 68, g32p_row03_traceSegment_071_1890_0067, g32p_row03_traceSegment_071_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 2025 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2049 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2041 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2041 8 9, g32p_row03_traceSegment_071_2041_0008, g32p_row03_traceSegment_071_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 2025 33 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2025 16 17, g32p_row03_traceSegment_071_2025_0016, g32p_row03_traceSegment_071_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2058 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2058 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2058 8 9, g32p_row03_traceSegment_071_2058_0008, g32p_row03_traceSegment_071_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2075 8 9, g32p_row03_traceSegment_071_2075_0008, g32p_row03_traceSegment_071_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2058 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2058 17 17, g32p_row03_traceSegment_071_2058_0017, g32p_row03_traceSegment_071_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 2025 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2025 33 34, g32p_row03_traceSegment_071_2025_0033, g32p_row03_traceSegment_071_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2092 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2092 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2092 8 9, g32p_row03_traceSegment_071_2092_0008, g32p_row03_traceSegment_071_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2109 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2109 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2109 8 9, g32p_row03_traceSegment_071_2109_0008, g32p_row03_traceSegment_071_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2092 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2092 17 17, g32p_row03_traceSegment_071_2092_0017, g32p_row03_traceSegment_071_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2126 8 9, g32p_row03_traceSegment_071_2126_0008, g32p_row03_traceSegment_071_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2143 8 9, g32p_row03_traceSegment_071_2143_0008, g32p_row03_traceSegment_071_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2126 17 17, g32p_row03_traceSegment_071_2126_0017, g32p_row03_traceSegment_071_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 2092 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2092 34 34, g32p_row03_traceSegment_071_2092_0034, g32p_row03_traceSegment_071_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 2025 135 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2025 67 68, g32p_row03_traceSegment_071_2025_0067, g32p_row03_traceSegment_071_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 1890 270 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1890 135 135, g32p_row03_traceSegment_071_1890_0135, g32p_row03_traceSegment_071_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_071 1620 540 = [0, 0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1620 270 270, g32p_row03_traceSegment_071_1620_0270, g32p_row03_traceSegment_071_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_071_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_071 1080 1080 = [0, 0, 0, 39] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 1080 540 540, g32p_row03_traceSegment_071_1080_0540, g32p_row03_traceSegment_071_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_071 0 2160 = [0, 0, 0, 57] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 0 1080 1080, g32p_row03_traceSegment_071_0000_1080, g32p_row03_traceSegment_071_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2176 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2184 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2176 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2176 8 9, g32p_row03_traceSegment_071_2176_0008, g32p_row03_traceSegment_071_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 2160 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2160 16 17, g32p_row03_traceSegment_071_2160_0016, g32p_row03_traceSegment_071_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2193 8 9, g32p_row03_traceSegment_071_2193_0008, g32p_row03_traceSegment_071_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2218 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2210 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2210 8 9, g32p_row03_traceSegment_071_2210_0008, g32p_row03_traceSegment_071_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2193 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2193 17 17, g32p_row03_traceSegment_071_2193_0017, g32p_row03_traceSegment_071_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 2160 67 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2160 33 34, g32p_row03_traceSegment_071_2160_0033, g32p_row03_traceSegment_071_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2227 8 9, g32p_row03_traceSegment_071_2227_0008, g32p_row03_traceSegment_071_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2252 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2244 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2244 8 9, g32p_row03_traceSegment_071_2244_0008, g32p_row03_traceSegment_071_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2227 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2227 17 17, g32p_row03_traceSegment_071_2227_0017, g32p_row03_traceSegment_071_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2261 8 9, g32p_row03_traceSegment_071_2261_0008, g32p_row03_traceSegment_071_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2278 8 9, g32p_row03_traceSegment_071_2278_0008, g32p_row03_traceSegment_071_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2261 17 17, g32p_row03_traceSegment_071_2261_0017, g32p_row03_traceSegment_071_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 2227 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2227 34 34, g32p_row03_traceSegment_071_2227_0034, g32p_row03_traceSegment_071_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 2160 135 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2160 67 68, g32p_row03_traceSegment_071_2160_0067, g32p_row03_traceSegment_071_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2311 8 9, g32p_row03_traceSegment_071_2311_0008, g32p_row03_traceSegment_071_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2295 16 17, g32p_row03_traceSegment_071_2295_0016, g32p_row03_traceSegment_071_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2328 8 9, g32p_row03_traceSegment_071_2328_0008, g32p_row03_traceSegment_071_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2345 8 9, g32p_row03_traceSegment_071_2345_0008, g32p_row03_traceSegment_071_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2328 17 17, g32p_row03_traceSegment_071_2328_0017, g32p_row03_traceSegment_071_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2295 33 34, g32p_row03_traceSegment_071_2295_0033, g32p_row03_traceSegment_071_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2362 8 9, g32p_row03_traceSegment_071_2362_0008, g32p_row03_traceSegment_071_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2379 8 9, g32p_row03_traceSegment_071_2379_0008, g32p_row03_traceSegment_071_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2362 17 17, g32p_row03_traceSegment_071_2362_0017, g32p_row03_traceSegment_071_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2396 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2396 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2396 8 9, g32p_row03_traceSegment_071_2396_0008, g32p_row03_traceSegment_071_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2413 8 9, g32p_row03_traceSegment_071_2413_0008, g32p_row03_traceSegment_071_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2396 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2396 17 17, g32p_row03_traceSegment_071_2396_0017, g32p_row03_traceSegment_071_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 2362 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2362 34 34, g32p_row03_traceSegment_071_2362_0034, g32p_row03_traceSegment_071_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 2295 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2295 67 68, g32p_row03_traceSegment_071_2295_0067, g32p_row03_traceSegment_071_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 2160 270 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2160 135 135, g32p_row03_traceSegment_071_2160_0135, g32p_row03_traceSegment_071_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2446 8 9, g32p_row03_traceSegment_071_2446_0008, g32p_row03_traceSegment_071_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2430 16 17, g32p_row03_traceSegment_071_2430_0016, g32p_row03_traceSegment_071_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2463 8 9, g32p_row03_traceSegment_071_2463_0008, g32p_row03_traceSegment_071_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2480 8 9, g32p_row03_traceSegment_071_2480_0008, g32p_row03_traceSegment_071_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2463 17 17, g32p_row03_traceSegment_071_2463_0017, g32p_row03_traceSegment_071_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2430 33 34, g32p_row03_traceSegment_071_2430_0033, g32p_row03_traceSegment_071_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2497 8 9, g32p_row03_traceSegment_071_2497_0008, g32p_row03_traceSegment_071_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2514 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2514 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2514 8 9, g32p_row03_traceSegment_071_2514_0008, g32p_row03_traceSegment_071_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2497 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2497 17 17, g32p_row03_traceSegment_071_2497_0017, g32p_row03_traceSegment_071_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2531 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2531 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2531 8 9, g32p_row03_traceSegment_071_2531_0008, g32p_row03_traceSegment_071_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2548 8 9, g32p_row03_traceSegment_071_2548_0008, g32p_row03_traceSegment_071_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2531 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2531 17 17, g32p_row03_traceSegment_071_2531_0017, g32p_row03_traceSegment_071_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 2497 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2497 34 34, g32p_row03_traceSegment_071_2497_0034, g32p_row03_traceSegment_071_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 2430 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2430 67 68, g32p_row03_traceSegment_071_2430_0067, g32p_row03_traceSegment_071_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2581 8 9, g32p_row03_traceSegment_071_2581_0008, g32p_row03_traceSegment_071_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2565 16 17, g32p_row03_traceSegment_071_2565_0016, g32p_row03_traceSegment_071_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2606 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2598 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2598 8 9, g32p_row03_traceSegment_071_2598_0008, g32p_row03_traceSegment_071_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2615 8 9, g32p_row03_traceSegment_071_2615_0008, g32p_row03_traceSegment_071_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2598 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2598 17 17, g32p_row03_traceSegment_071_2598_0017, g32p_row03_traceSegment_071_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 2565 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2565 33 34, g32p_row03_traceSegment_071_2565_0033, g32p_row03_traceSegment_071_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2632 8 9, g32p_row03_traceSegment_071_2632_0008, g32p_row03_traceSegment_071_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2649 8 9, g32p_row03_traceSegment_071_2649_0008, g32p_row03_traceSegment_071_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2632 17 17, g32p_row03_traceSegment_071_2632_0017, g32p_row03_traceSegment_071_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2666 8 9, g32p_row03_traceSegment_071_2666_0008, g32p_row03_traceSegment_071_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2683 8 9, g32p_row03_traceSegment_071_2683_0008, g32p_row03_traceSegment_071_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2666 17 17, g32p_row03_traceSegment_071_2666_0017, g32p_row03_traceSegment_071_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2632 34 34, g32p_row03_traceSegment_071_2632_0034, g32p_row03_traceSegment_071_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 2565 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2565 67 68, g32p_row03_traceSegment_071_2565_0067, g32p_row03_traceSegment_071_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 2430 270 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2430 135 135, g32p_row03_traceSegment_071_2430_0135, g32p_row03_traceSegment_071_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_071 2160 540 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2160 270 270, g32p_row03_traceSegment_071_2160_0270, g32p_row03_traceSegment_071_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2716 8 9, g32p_row03_traceSegment_071_2716_0008, g32p_row03_traceSegment_071_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2700 16 17, g32p_row03_traceSegment_071_2700_0016, g32p_row03_traceSegment_071_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2733 8 9, g32p_row03_traceSegment_071_2733_0008, g32p_row03_traceSegment_071_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2758 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2750 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2750 8 9, g32p_row03_traceSegment_071_2750_0008, g32p_row03_traceSegment_071_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2733 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2733 17 17, g32p_row03_traceSegment_071_2733_0017, g32p_row03_traceSegment_071_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 2700 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2700 33 34, g32p_row03_traceSegment_071_2700_0033, g32p_row03_traceSegment_071_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2767 8 9, g32p_row03_traceSegment_071_2767_0008, g32p_row03_traceSegment_071_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2792 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2784 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2784 8 9, g32p_row03_traceSegment_071_2784_0008, g32p_row03_traceSegment_071_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2767 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2767 17 17, g32p_row03_traceSegment_071_2767_0017, g32p_row03_traceSegment_071_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2801 8 9, g32p_row03_traceSegment_071_2801_0008, g32p_row03_traceSegment_071_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2818 8 9, g32p_row03_traceSegment_071_2818_0008, g32p_row03_traceSegment_071_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2801 17 17, g32p_row03_traceSegment_071_2801_0017, g32p_row03_traceSegment_071_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 2767 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2767 34 34, g32p_row03_traceSegment_071_2767_0034, g32p_row03_traceSegment_071_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 2700 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2700 67 68, g32p_row03_traceSegment_071_2700_0067, g32p_row03_traceSegment_071_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 2835 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2851 8 9, g32p_row03_traceSegment_071_2851_0008, g32p_row03_traceSegment_071_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 2835 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2835 16 17, g32p_row03_traceSegment_071_2835_0016, g32p_row03_traceSegment_071_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2876 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2868 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2868 8 9, g32p_row03_traceSegment_071_2868_0008, g32p_row03_traceSegment_071_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2885 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2885 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2885 8 9, g32p_row03_traceSegment_071_2885_0008, g32p_row03_traceSegment_071_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2868 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2868 17 17, g32p_row03_traceSegment_071_2868_0017, g32p_row03_traceSegment_071_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 2835 67 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2835 33 34, g32p_row03_traceSegment_071_2835_0033, g32p_row03_traceSegment_071_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2902 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2902 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2902 8 9, g32p_row03_traceSegment_071_2902_0008, g32p_row03_traceSegment_071_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2927 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2919 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2919 8 9, g32p_row03_traceSegment_071_2919_0008, g32p_row03_traceSegment_071_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2902 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2902 17 17, g32p_row03_traceSegment_071_2902_0017, g32p_row03_traceSegment_071_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2936 8 9, g32p_row03_traceSegment_071_2936_0008, g32p_row03_traceSegment_071_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2953 8 9, g32p_row03_traceSegment_071_2953_0008, g32p_row03_traceSegment_071_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2936 17 17, g32p_row03_traceSegment_071_2936_0017, g32p_row03_traceSegment_071_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 2902 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2902 34 34, g32p_row03_traceSegment_071_2902_0034, g32p_row03_traceSegment_071_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 2835 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2835 67 68, g32p_row03_traceSegment_071_2835_0067, g32p_row03_traceSegment_071_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 2700 270 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2700 135 135, g32p_row03_traceSegment_071_2700_0135, g32p_row03_traceSegment_071_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2986 8 9, g32p_row03_traceSegment_071_2986_0008, g32p_row03_traceSegment_071_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2970 16 17, g32p_row03_traceSegment_071_2970_0016, g32p_row03_traceSegment_071_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3003 8 9, g32p_row03_traceSegment_071_3003_0008, g32p_row03_traceSegment_071_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3020 8 9, g32p_row03_traceSegment_071_3020_0008, g32p_row03_traceSegment_071_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3003 17 17, g32p_row03_traceSegment_071_3003_0017, g32p_row03_traceSegment_071_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2970 33 34, g32p_row03_traceSegment_071_2970_0033, g32p_row03_traceSegment_071_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3045 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3037 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3037 8 9, g32p_row03_traceSegment_071_3037_0008, g32p_row03_traceSegment_071_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3054 8 9, g32p_row03_traceSegment_071_3054_0008, g32p_row03_traceSegment_071_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3037 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3037 17 17, g32p_row03_traceSegment_071_3037_0017, g32p_row03_traceSegment_071_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3079 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3071 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3071 8 9, g32p_row03_traceSegment_071_3071_0008, g32p_row03_traceSegment_071_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3088 8 9, g32p_row03_traceSegment_071_3088_0008, g32p_row03_traceSegment_071_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3071 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3071 17 17, g32p_row03_traceSegment_071_3071_0017, g32p_row03_traceSegment_071_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 3037 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3037 34 34, g32p_row03_traceSegment_071_3037_0034, g32p_row03_traceSegment_071_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 2970 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2970 67 68, g32p_row03_traceSegment_071_2970_0067, g32p_row03_traceSegment_071_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3129 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3121 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3121 8 9, g32p_row03_traceSegment_071_3121_0008, g32p_row03_traceSegment_071_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 3105 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3105 16 17, g32p_row03_traceSegment_071_3105_0016, g32p_row03_traceSegment_071_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3138 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3146 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3138 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3138 8 9, g32p_row03_traceSegment_071_3138_0008, g32p_row03_traceSegment_071_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3155 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3163 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3155 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3155 8 9, g32p_row03_traceSegment_071_3155_0008, g32p_row03_traceSegment_071_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3138 34 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3138 17 17, g32p_row03_traceSegment_071_3138_0017, g32p_row03_traceSegment_071_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 3105 67 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3105 33 34, g32p_row03_traceSegment_071_3105_0033, g32p_row03_traceSegment_071_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3180 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3172 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3172 8 9, g32p_row03_traceSegment_071_3172_0008, g32p_row03_traceSegment_071_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3197 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3189 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3189 8 9, g32p_row03_traceSegment_071_3189_0008, g32p_row03_traceSegment_071_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3172 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3172 17 17, g32p_row03_traceSegment_071_3172_0017, g32p_row03_traceSegment_071_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3206 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3214 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3206 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3206 8 9, g32p_row03_traceSegment_071_3206_0008, g32p_row03_traceSegment_071_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3223 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3231 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3223 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3223 8 9, g32p_row03_traceSegment_071_3223_0008, g32p_row03_traceSegment_071_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3206 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3206 17 17, g32p_row03_traceSegment_071_3206_0017, g32p_row03_traceSegment_071_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 3172 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3172 34 34, g32p_row03_traceSegment_071_3172_0034, g32p_row03_traceSegment_071_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 3105 135 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3105 67 68, g32p_row03_traceSegment_071_3105_0067, g32p_row03_traceSegment_071_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 2970 270 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2970 135 135, g32p_row03_traceSegment_071_2970_0135, g32p_row03_traceSegment_071_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_071 2700 540 = [0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2700 270 270, g32p_row03_traceSegment_071_2700_0270, g32p_row03_traceSegment_071_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_071 2160 1080 = [0, 0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2160 540 540, g32p_row03_traceSegment_071_2160_0540, g32p_row03_traceSegment_071_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 3240 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3256 8 9, g32p_row03_traceSegment_071_3256_0008, g32p_row03_traceSegment_071_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 3240 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3240 16 17, g32p_row03_traceSegment_071_3240_0016, g32p_row03_traceSegment_071_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3273 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3281 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3273 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3273 8 9, g32p_row03_traceSegment_071_3273_0008, g32p_row03_traceSegment_071_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3290 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3298 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3290 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3290 8 9, g32p_row03_traceSegment_071_3290_0008, g32p_row03_traceSegment_071_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3273 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3273 17 17, g32p_row03_traceSegment_071_3273_0017, g32p_row03_traceSegment_071_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 3240 67 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3240 33 34, g32p_row03_traceSegment_071_3240_0033, g32p_row03_traceSegment_071_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3307 8 9, g32p_row03_traceSegment_071_3307_0008, g32p_row03_traceSegment_071_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3324 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3332 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3324 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3324 8 9, g32p_row03_traceSegment_071_3324_0008, g32p_row03_traceSegment_071_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3307 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3307 17 17, g32p_row03_traceSegment_071_3307_0017, g32p_row03_traceSegment_071_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3341 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3349 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3341 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3341 8 9, g32p_row03_traceSegment_071_3341_0008, g32p_row03_traceSegment_071_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3358 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3358 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3358 8 9, g32p_row03_traceSegment_071_3358_0008, g32p_row03_traceSegment_071_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3341 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3341 17 17, g32p_row03_traceSegment_071_3341_0017, g32p_row03_traceSegment_071_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 3307 68 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3307 34 34, g32p_row03_traceSegment_071_3307_0034, g32p_row03_traceSegment_071_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 3240 135 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3240 67 68, g32p_row03_traceSegment_071_3240_0067, g32p_row03_traceSegment_071_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3391 8 9, g32p_row03_traceSegment_071_3391_0008, g32p_row03_traceSegment_071_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3375 16 17, g32p_row03_traceSegment_071_3375_0016, g32p_row03_traceSegment_071_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3408 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3408 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3408 8 9, g32p_row03_traceSegment_071_3408_0008, g32p_row03_traceSegment_071_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3425 8 9, g32p_row03_traceSegment_071_3425_0008, g32p_row03_traceSegment_071_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3408 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3408 17 17, g32p_row03_traceSegment_071_3408_0017, g32p_row03_traceSegment_071_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 3375 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3375 33 34, g32p_row03_traceSegment_071_3375_0033, g32p_row03_traceSegment_071_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3442 8 9, g32p_row03_traceSegment_071_3442_0008, g32p_row03_traceSegment_071_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3459 8 9, g32p_row03_traceSegment_071_3459_0008, g32p_row03_traceSegment_071_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3442 17 17, g32p_row03_traceSegment_071_3442_0017, g32p_row03_traceSegment_071_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3484 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3476 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3476 8 9, g32p_row03_traceSegment_071_3476_0008, g32p_row03_traceSegment_071_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3501 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3493 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3493 8 9, g32p_row03_traceSegment_071_3493_0008, g32p_row03_traceSegment_071_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3476 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3476 17 17, g32p_row03_traceSegment_071_3476_0017, g32p_row03_traceSegment_071_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 3442 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3442 34 34, g32p_row03_traceSegment_071_3442_0034, g32p_row03_traceSegment_071_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 3375 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3375 67 68, g32p_row03_traceSegment_071_3375_0067, g32p_row03_traceSegment_071_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 3240 270 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3240 135 135, g32p_row03_traceSegment_071_3240_0135, g32p_row03_traceSegment_071_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3534 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3526 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3526 8 9, g32p_row03_traceSegment_071_3526_0008, g32p_row03_traceSegment_071_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 3510 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3510 16 17, g32p_row03_traceSegment_071_3510_0016, g32p_row03_traceSegment_071_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3543 8 9, g32p_row03_traceSegment_071_3543_0008, g32p_row03_traceSegment_071_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3560 8 9, g32p_row03_traceSegment_071_3560_0008, g32p_row03_traceSegment_071_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3543 17 17, g32p_row03_traceSegment_071_3543_0017, g32p_row03_traceSegment_071_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 3510 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3510 33 34, g32p_row03_traceSegment_071_3510_0033, g32p_row03_traceSegment_071_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3577 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3585 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3577 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3577 8 9, g32p_row03_traceSegment_071_3577_0008, g32p_row03_traceSegment_071_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3594 8 9, g32p_row03_traceSegment_071_3594_0008, g32p_row03_traceSegment_071_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3577 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3577 17 17, g32p_row03_traceSegment_071_3577_0017, g32p_row03_traceSegment_071_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3611 8 9, g32p_row03_traceSegment_071_3611_0008, g32p_row03_traceSegment_071_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3636 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3628 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3628 8 9, g32p_row03_traceSegment_071_3628_0008, g32p_row03_traceSegment_071_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3611 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3611 17 17, g32p_row03_traceSegment_071_3611_0017, g32p_row03_traceSegment_071_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 3577 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3577 34 34, g32p_row03_traceSegment_071_3577_0034, g32p_row03_traceSegment_071_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 3510 135 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3510 67 68, g32p_row03_traceSegment_071_3510_0067, g32p_row03_traceSegment_071_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 3645 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3661 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3661 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3661 8 9, g32p_row03_traceSegment_071_3661_0008, g32p_row03_traceSegment_071_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 3645 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3645 16 17, g32p_row03_traceSegment_071_3645_0016, g32p_row03_traceSegment_071_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3678 8 9, g32p_row03_traceSegment_071_3678_0008, g32p_row03_traceSegment_071_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3695 8 9, g32p_row03_traceSegment_071_3695_0008, g32p_row03_traceSegment_071_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3678 17 17, g32p_row03_traceSegment_071_3678_0017, g32p_row03_traceSegment_071_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 3645 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3645 33 34, g32p_row03_traceSegment_071_3645_0033, g32p_row03_traceSegment_071_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3712 8 9, g32p_row03_traceSegment_071_3712_0008, g32p_row03_traceSegment_071_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3729 8 9, g32p_row03_traceSegment_071_3729_0008, g32p_row03_traceSegment_071_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3712 17 17, g32p_row03_traceSegment_071_3712_0017, g32p_row03_traceSegment_071_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3746 8 9, g32p_row03_traceSegment_071_3746_0008, g32p_row03_traceSegment_071_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3763 8 9, g32p_row03_traceSegment_071_3763_0008, g32p_row03_traceSegment_071_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3746 17 17, g32p_row03_traceSegment_071_3746_0017, g32p_row03_traceSegment_071_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3712 34 34, g32p_row03_traceSegment_071_3712_0034, g32p_row03_traceSegment_071_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 3645 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3645 67 68, g32p_row03_traceSegment_071_3645_0067, g32p_row03_traceSegment_071_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 3510 270 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3510 135 135, g32p_row03_traceSegment_071_3510_0135, g32p_row03_traceSegment_071_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_071 3240 540 = [0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3240 270 270, g32p_row03_traceSegment_071_3240_0270, g32p_row03_traceSegment_071_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3796 8 9, g32p_row03_traceSegment_071_3796_0008, g32p_row03_traceSegment_071_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3780 16 17, g32p_row03_traceSegment_071_3780_0016, g32p_row03_traceSegment_071_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3813 8 9, g32p_row03_traceSegment_071_3813_0008, g32p_row03_traceSegment_071_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3830 8 9, g32p_row03_traceSegment_071_3830_0008, g32p_row03_traceSegment_071_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3813 17 17, g32p_row03_traceSegment_071_3813_0017, g32p_row03_traceSegment_071_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3780 33 34, g32p_row03_traceSegment_071_3780_0033, g32p_row03_traceSegment_071_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3847 8 9, g32p_row03_traceSegment_071_3847_0008, g32p_row03_traceSegment_071_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3864 8 9, g32p_row03_traceSegment_071_3864_0008, g32p_row03_traceSegment_071_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3847 17 17, g32p_row03_traceSegment_071_3847_0017, g32p_row03_traceSegment_071_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3881 8 9, g32p_row03_traceSegment_071_3881_0008, g32p_row03_traceSegment_071_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3898 8 9, g32p_row03_traceSegment_071_3898_0008, g32p_row03_traceSegment_071_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3881 17 17, g32p_row03_traceSegment_071_3881_0017, g32p_row03_traceSegment_071_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3847 34 34, g32p_row03_traceSegment_071_3847_0034, g32p_row03_traceSegment_071_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3780 67 68, g32p_row03_traceSegment_071_3780_0067, g32p_row03_traceSegment_071_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3931 8 9, g32p_row03_traceSegment_071_3931_0008, g32p_row03_traceSegment_071_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3915 16 17, g32p_row03_traceSegment_071_3915_0016, g32p_row03_traceSegment_071_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3948 8 9, g32p_row03_traceSegment_071_3948_0008, g32p_row03_traceSegment_071_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3965 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3965 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3965 8 9, g32p_row03_traceSegment_071_3965_0008, g32p_row03_traceSegment_071_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3948 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3948 17 17, g32p_row03_traceSegment_071_3948_0017, g32p_row03_traceSegment_071_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 3915 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3915 33 34, g32p_row03_traceSegment_071_3915_0033, g32p_row03_traceSegment_071_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3982 8 9, g32p_row03_traceSegment_071_3982_0008, g32p_row03_traceSegment_071_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3999 8 9, g32p_row03_traceSegment_071_3999_0008, g32p_row03_traceSegment_071_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3982 17 17, g32p_row03_traceSegment_071_3982_0017, g32p_row03_traceSegment_071_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4016 8 9, g32p_row03_traceSegment_071_4016_0008, g32p_row03_traceSegment_071_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4033 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4033 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4033 8 9, g32p_row03_traceSegment_071_4033_0008, g32p_row03_traceSegment_071_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 4016 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4016 17 17, g32p_row03_traceSegment_071_4016_0017, g32p_row03_traceSegment_071_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 3982 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3982 34 34, g32p_row03_traceSegment_071_3982_0034, g32p_row03_traceSegment_071_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 3915 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3915 67 68, g32p_row03_traceSegment_071_3915_0067, g32p_row03_traceSegment_071_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 3780 270 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3780 135 135, g32p_row03_traceSegment_071_3780_0135, g32p_row03_traceSegment_071_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4066 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4066 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4066 8 9, g32p_row03_traceSegment_071_4066_0008, g32p_row03_traceSegment_071_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 4050 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4050 16 17, g32p_row03_traceSegment_071_4050_0016, g32p_row03_traceSegment_071_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4083 8 9, g32p_row03_traceSegment_071_4083_0008, g32p_row03_traceSegment_071_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4100 8 9, g32p_row03_traceSegment_071_4100_0008, g32p_row03_traceSegment_071_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4083 17 17, g32p_row03_traceSegment_071_4083_0017, g32p_row03_traceSegment_071_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 4050 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4050 33 34, g32p_row03_traceSegment_071_4050_0033, g32p_row03_traceSegment_071_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4117 8 9, g32p_row03_traceSegment_071_4117_0008, g32p_row03_traceSegment_071_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4134 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4134 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4134 8 9, g32p_row03_traceSegment_071_4134_0008, g32p_row03_traceSegment_071_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 4117 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4117 17 17, g32p_row03_traceSegment_071_4117_0017, g32p_row03_traceSegment_071_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4151 8 9, g32p_row03_traceSegment_071_4151_0008, g32p_row03_traceSegment_071_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4168 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4176 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4168 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4168 8 9, g32p_row03_traceSegment_071_4168_0008, g32p_row03_traceSegment_071_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 4151 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4151 17 17, g32p_row03_traceSegment_071_4151_0017, g32p_row03_traceSegment_071_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 4117 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4117 34 34, g32p_row03_traceSegment_071_4117_0034, g32p_row03_traceSegment_071_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 4050 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4050 67 68, g32p_row03_traceSegment_071_4050_0067, g32p_row03_traceSegment_071_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_071 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4209 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4201 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4201 8 9, g32p_row03_traceSegment_071_4201_0008, g32p_row03_traceSegment_071_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_071 4185 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4185 16 17, g32p_row03_traceSegment_071_4185_0016, g32p_row03_traceSegment_071_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4226 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4218 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4218 8 9, g32p_row03_traceSegment_071_4218_0008, g32p_row03_traceSegment_071_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4235 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4235 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4235 8 9, g32p_row03_traceSegment_071_4235_0008, g32p_row03_traceSegment_071_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 4218 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4218 17 17, g32p_row03_traceSegment_071_4218_0017, g32p_row03_traceSegment_071_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_071 4185 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4185 33 34, g32p_row03_traceSegment_071_4185_0033, g32p_row03_traceSegment_071_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4252 8 9, g32p_row03_traceSegment_071_4252_0008, g32p_row03_traceSegment_071_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4269 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4269 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4269 8 9, g32p_row03_traceSegment_071_4269_0008, g32p_row03_traceSegment_071_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 4252 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4252 17 17, g32p_row03_traceSegment_071_4252_0017, g32p_row03_traceSegment_071_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4286 8 9, g32p_row03_traceSegment_071_4286_0008, g32p_row03_traceSegment_071_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_071 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_071 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_071_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_071 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4303 8 9, g32p_row03_traceSegment_071_4303_0008, g32p_row03_traceSegment_071_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_071 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4286 17 17, g32p_row03_traceSegment_071_4286_0017, g32p_row03_traceSegment_071_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_071 4252 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4252 34 34, g32p_row03_traceSegment_071_4252_0034, g32p_row03_traceSegment_071_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_071 4185 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4185 67 68, g32p_row03_traceSegment_071_4185_0067, g32p_row03_traceSegment_071_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_071_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_071 4050 270 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 4050 135 135, g32p_row03_traceSegment_071_4050_0135, g32p_row03_traceSegment_071_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_071 3780 540 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3780 270 270, g32p_row03_traceSegment_071_3780_0270, g32p_row03_traceSegment_071_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_071_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_071 3240 1080 = [0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 3240 540 540, g32p_row03_traceSegment_071_3240_0540, g32p_row03_traceSegment_071_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_071_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_071 2160 2160 = [0, 0, 0, 63] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 2160 1080 1080, g32p_row03_traceSegment_071_2160_1080, g32p_row03_traceSegment_071_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_071_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_071 0 4320 = [0, 0, 0, 120] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_071 0 2160 2160, g32p_row03_traceSegment_071_0000_2160, g32p_row03_traceSegment_071_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 71 = [0, 0, 0, 120] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_071_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_073 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 73 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_073_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 16 8 9, g32p_row03_traceSegment_073_0016_0008, g32p_row03_traceSegment_073_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 0 16 17, g32p_row03_traceSegment_073_0000_0016, g32p_row03_traceSegment_073_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 33 8 9, g32p_row03_traceSegment_073_0033_0008, g32p_row03_traceSegment_073_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 50 8 9, g32p_row03_traceSegment_073_0050_0008, g32p_row03_traceSegment_073_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 33 17 17, g32p_row03_traceSegment_073_0033_0017, g32p_row03_traceSegment_073_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 0 33 34, g32p_row03_traceSegment_073_0000_0033, g32p_row03_traceSegment_073_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 67 8 9, g32p_row03_traceSegment_073_0067_0008, g32p_row03_traceSegment_073_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 84 8 9, g32p_row03_traceSegment_073_0084_0008, g32p_row03_traceSegment_073_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 67 17 17, g32p_row03_traceSegment_073_0067_0017, g32p_row03_traceSegment_073_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 101 8 9, g32p_row03_traceSegment_073_0101_0008, g32p_row03_traceSegment_073_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 126 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 118 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 118 8 9, g32p_row03_traceSegment_073_0118_0008, g32p_row03_traceSegment_073_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 101 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 101 17 17, g32p_row03_traceSegment_073_0101_0017, g32p_row03_traceSegment_073_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 67 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 67 34 34, g32p_row03_traceSegment_073_0067_0034, g32p_row03_traceSegment_073_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 0 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 0 67 68, g32p_row03_traceSegment_073_0000_0067, g32p_row03_traceSegment_073_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 135 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 151 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 159 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 151 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 151 8 9, g32p_row03_traceSegment_073_0151_0008, g32p_row03_traceSegment_073_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 135 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 135 16 17, g32p_row03_traceSegment_073_0135_0016, g32p_row03_traceSegment_073_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 168 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 168 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 168 8 9, g32p_row03_traceSegment_073_0168_0008, g32p_row03_traceSegment_073_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 185 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 193 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 185 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 185 8 9, g32p_row03_traceSegment_073_0185_0008, g32p_row03_traceSegment_073_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 168 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 168 17 17, g32p_row03_traceSegment_073_0168_0017, g32p_row03_traceSegment_073_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 135 67 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 135 33 34, g32p_row03_traceSegment_073_0135_0033, g32p_row03_traceSegment_073_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 202 8 9, g32p_row03_traceSegment_073_0202_0008, g32p_row03_traceSegment_073_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 219 8 9, g32p_row03_traceSegment_073_0219_0008, g32p_row03_traceSegment_073_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 202 17 17, g32p_row03_traceSegment_073_0202_0017, g32p_row03_traceSegment_073_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 236 8 9, g32p_row03_traceSegment_073_0236_0008, g32p_row03_traceSegment_073_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 253 8 9, g32p_row03_traceSegment_073_0253_0008, g32p_row03_traceSegment_073_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 236 17 17, g32p_row03_traceSegment_073_0236_0017, g32p_row03_traceSegment_073_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 202 34 34, g32p_row03_traceSegment_073_0202_0034, g32p_row03_traceSegment_073_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 135 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 135 67 68, g32p_row03_traceSegment_073_0135_0067, g32p_row03_traceSegment_073_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 0 270 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 0 135 135, g32p_row03_traceSegment_073_0000_0135, g32p_row03_traceSegment_073_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 286 8 9, g32p_row03_traceSegment_073_0286_0008, g32p_row03_traceSegment_073_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 270 16 17, g32p_row03_traceSegment_073_0270_0016, g32p_row03_traceSegment_073_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 303 8 9, g32p_row03_traceSegment_073_0303_0008, g32p_row03_traceSegment_073_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 320 8 9, g32p_row03_traceSegment_073_0320_0008, g32p_row03_traceSegment_073_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 303 17 17, g32p_row03_traceSegment_073_0303_0017, g32p_row03_traceSegment_073_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 270 33 34, g32p_row03_traceSegment_073_0270_0033, g32p_row03_traceSegment_073_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 337 8 9, g32p_row03_traceSegment_073_0337_0008, g32p_row03_traceSegment_073_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 354 8 9, g32p_row03_traceSegment_073_0354_0008, g32p_row03_traceSegment_073_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 337 17 17, g32p_row03_traceSegment_073_0337_0017, g32p_row03_traceSegment_073_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 371 8 9, g32p_row03_traceSegment_073_0371_0008, g32p_row03_traceSegment_073_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 388 8 9, g32p_row03_traceSegment_073_0388_0008, g32p_row03_traceSegment_073_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 371 17 17, g32p_row03_traceSegment_073_0371_0017, g32p_row03_traceSegment_073_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 337 34 34, g32p_row03_traceSegment_073_0337_0034, g32p_row03_traceSegment_073_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 270 67 68, g32p_row03_traceSegment_073_0270_0067, g32p_row03_traceSegment_073_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 429 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 421 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 421 8 9, g32p_row03_traceSegment_073_0421_0008, g32p_row03_traceSegment_073_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 405 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 405 16 17, g32p_row03_traceSegment_073_0405_0016, g32p_row03_traceSegment_073_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 438 8 9, g32p_row03_traceSegment_073_0438_0008, g32p_row03_traceSegment_073_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 455 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 463 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 455 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 455 8 9, g32p_row03_traceSegment_073_0455_0008, g32p_row03_traceSegment_073_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 438 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 438 17 17, g32p_row03_traceSegment_073_0438_0017, g32p_row03_traceSegment_073_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 405 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 405 33 34, g32p_row03_traceSegment_073_0405_0033, g32p_row03_traceSegment_073_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 472 8 9, g32p_row03_traceSegment_073_0472_0008, g32p_row03_traceSegment_073_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 497 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 489 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 489 8 9, g32p_row03_traceSegment_073_0489_0008, g32p_row03_traceSegment_073_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 472 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 472 17 17, g32p_row03_traceSegment_073_0472_0017, g32p_row03_traceSegment_073_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 506 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 514 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 506 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 506 8 9, g32p_row03_traceSegment_073_0506_0008, g32p_row03_traceSegment_073_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 523 8 9, g32p_row03_traceSegment_073_0523_0008, g32p_row03_traceSegment_073_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 506 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 506 17 17, g32p_row03_traceSegment_073_0506_0017, g32p_row03_traceSegment_073_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 472 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 472 34 34, g32p_row03_traceSegment_073_0472_0034, g32p_row03_traceSegment_073_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 405 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 405 67 68, g32p_row03_traceSegment_073_0405_0067, g32p_row03_traceSegment_073_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 270 270 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 270 135 135, g32p_row03_traceSegment_073_0270_0135, g32p_row03_traceSegment_073_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_073 0 540 = [13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 0 270 270, g32p_row03_traceSegment_073_0000_0270, g32p_row03_traceSegment_073_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 556 8 9, g32p_row03_traceSegment_073_0556_0008, g32p_row03_traceSegment_073_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 540 16 17, g32p_row03_traceSegment_073_0540_0016, g32p_row03_traceSegment_073_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 581 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 573 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 573 8 9, g32p_row03_traceSegment_073_0573_0008, g32p_row03_traceSegment_073_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 590 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 590 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 590 8 9, g32p_row03_traceSegment_073_0590_0008, g32p_row03_traceSegment_073_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 573 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 573 17 17, g32p_row03_traceSegment_073_0573_0017, g32p_row03_traceSegment_073_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 540 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 540 33 34, g32p_row03_traceSegment_073_0540_0033, g32p_row03_traceSegment_073_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 607 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 607 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 607 8 9, g32p_row03_traceSegment_073_0607_0008, g32p_row03_traceSegment_073_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 624 8 9, g32p_row03_traceSegment_073_0624_0008, g32p_row03_traceSegment_073_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 607 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 607 17 17, g32p_row03_traceSegment_073_0607_0017, g32p_row03_traceSegment_073_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 641 8 9, g32p_row03_traceSegment_073_0641_0008, g32p_row03_traceSegment_073_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 658 8 9, g32p_row03_traceSegment_073_0658_0008, g32p_row03_traceSegment_073_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 641 17 17, g32p_row03_traceSegment_073_0641_0017, g32p_row03_traceSegment_073_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 607 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 607 34 34, g32p_row03_traceSegment_073_0607_0034, g32p_row03_traceSegment_073_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 540 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 540 67 68, g32p_row03_traceSegment_073_0540_0067, g32p_row03_traceSegment_073_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 691 8 9, g32p_row03_traceSegment_073_0691_0008, g32p_row03_traceSegment_073_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 675 16 17, g32p_row03_traceSegment_073_0675_0016, g32p_row03_traceSegment_073_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 708 8 9, g32p_row03_traceSegment_073_0708_0008, g32p_row03_traceSegment_073_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 725 8 9, g32p_row03_traceSegment_073_0725_0008, g32p_row03_traceSegment_073_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 708 17 17, g32p_row03_traceSegment_073_0708_0017, g32p_row03_traceSegment_073_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 675 33 34, g32p_row03_traceSegment_073_0675_0033, g32p_row03_traceSegment_073_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 742 8 9, g32p_row03_traceSegment_073_0742_0008, g32p_row03_traceSegment_073_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 759 8 9, g32p_row03_traceSegment_073_0759_0008, g32p_row03_traceSegment_073_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 742 17 17, g32p_row03_traceSegment_073_0742_0017, g32p_row03_traceSegment_073_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 776 8 9, g32p_row03_traceSegment_073_0776_0008, g32p_row03_traceSegment_073_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 793 8 9, g32p_row03_traceSegment_073_0793_0008, g32p_row03_traceSegment_073_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 776 17 17, g32p_row03_traceSegment_073_0776_0017, g32p_row03_traceSegment_073_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 742 34 34, g32p_row03_traceSegment_073_0742_0034, g32p_row03_traceSegment_073_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 675 67 68, g32p_row03_traceSegment_073_0675_0067, g32p_row03_traceSegment_073_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 540 270 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 540 135 135, g32p_row03_traceSegment_073_0540_0135, g32p_row03_traceSegment_073_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 826 8 9, g32p_row03_traceSegment_073_0826_0008, g32p_row03_traceSegment_073_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 810 16 17, g32p_row03_traceSegment_073_0810_0016, g32p_row03_traceSegment_073_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 843 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 843 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 843 8 9, g32p_row03_traceSegment_073_0843_0008, g32p_row03_traceSegment_073_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 860 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 860 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 860 8 9, g32p_row03_traceSegment_073_0860_0008, g32p_row03_traceSegment_073_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 843 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 843 17 17, g32p_row03_traceSegment_073_0843_0017, g32p_row03_traceSegment_073_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 810 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 810 33 34, g32p_row03_traceSegment_073_0810_0033, g32p_row03_traceSegment_073_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 877 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 877 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 877 8 9, g32p_row03_traceSegment_073_0877_0008, g32p_row03_traceSegment_073_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 894 8 9, g32p_row03_traceSegment_073_0894_0008, g32p_row03_traceSegment_073_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 877 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 877 17 17, g32p_row03_traceSegment_073_0877_0017, g32p_row03_traceSegment_073_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 911 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 911 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 911 8 9, g32p_row03_traceSegment_073_0911_0008, g32p_row03_traceSegment_073_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 928 8 9, g32p_row03_traceSegment_073_0928_0008, g32p_row03_traceSegment_073_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 911 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 911 17 17, g32p_row03_traceSegment_073_0911_0017, g32p_row03_traceSegment_073_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 877 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 877 34 34, g32p_row03_traceSegment_073_0877_0034, g32p_row03_traceSegment_073_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 810 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 810 67 68, g32p_row03_traceSegment_073_0810_0067, g32p_row03_traceSegment_073_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 945 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 961 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 969 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 961 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 961 8 9, g32p_row03_traceSegment_073_0961_0008, g32p_row03_traceSegment_073_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 945 33 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 945 16 17, g32p_row03_traceSegment_073_0945_0016, g32p_row03_traceSegment_073_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 978 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 986 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 978 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 978 8 9, g32p_row03_traceSegment_073_0978_0008, g32p_row03_traceSegment_073_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 995 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1003 9 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 995 17 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 995 8 9, g32p_row03_traceSegment_073_0995_0008, g32p_row03_traceSegment_073_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 978 34 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 978 17 17, g32p_row03_traceSegment_073_0978_0017, g32p_row03_traceSegment_073_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 945 67 = [10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 945 33 34, g32p_row03_traceSegment_073_0945_0033, g32p_row03_traceSegment_073_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1012 8 9, g32p_row03_traceSegment_073_1012_0008, g32p_row03_traceSegment_073_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1029 8 9, g32p_row03_traceSegment_073_1029_0008, g32p_row03_traceSegment_073_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1012 17 17, g32p_row03_traceSegment_073_1012_0017, g32p_row03_traceSegment_073_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1046 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1054 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1046 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1046 8 9, g32p_row03_traceSegment_073_1046_0008, g32p_row03_traceSegment_073_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1063 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1063 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1063 8 9, g32p_row03_traceSegment_073_1063_0008, g32p_row03_traceSegment_073_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1046 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1046 17 17, g32p_row03_traceSegment_073_1046_0017, g32p_row03_traceSegment_073_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 1012 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1012 34 34, g32p_row03_traceSegment_073_1012_0034, g32p_row03_traceSegment_073_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 945 135 = [14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 945 67 68, g32p_row03_traceSegment_073_0945_0067, g32p_row03_traceSegment_073_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 810 270 = [19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 810 135 135, g32p_row03_traceSegment_073_0810_0135, g32p_row03_traceSegment_073_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_073 540 540 = [22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 540 270 270, g32p_row03_traceSegment_073_0540_0270, g32p_row03_traceSegment_073_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_073 0 1080 = [35] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 0 540 540, g32p_row03_traceSegment_073_0000_0540, g32p_row03_traceSegment_073_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 1080 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1096 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1104 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1096 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1096 8 9, g32p_row03_traceSegment_073_1096_0008, g32p_row03_traceSegment_073_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 1080 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1080 16 17, g32p_row03_traceSegment_073_1080_0016, g32p_row03_traceSegment_073_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1113 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1113 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1113 8 9, g32p_row03_traceSegment_073_1113_0008, g32p_row03_traceSegment_073_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1130 8 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1130 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1130 8 9, g32p_row03_traceSegment_073_1130_0008, g32p_row03_traceSegment_073_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1113 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1113 17 17, g32p_row03_traceSegment_073_1113_0017, g32p_row03_traceSegment_073_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 1080 67 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1080 33 34, g32p_row03_traceSegment_073_1080_0033, g32p_row03_traceSegment_073_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1155 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1147 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1147 8 9, g32p_row03_traceSegment_073_1147_0008, g32p_row03_traceSegment_073_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1164 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1172 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1164 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1164 8 9, g32p_row03_traceSegment_073_1164_0008, g32p_row03_traceSegment_073_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1147 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1147 17 17, g32p_row03_traceSegment_073_1147_0017, g32p_row03_traceSegment_073_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1181 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1189 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1181 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1181 8 9, g32p_row03_traceSegment_073_1181_0008, g32p_row03_traceSegment_073_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1198 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1198 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1198 8 9, g32p_row03_traceSegment_073_1198_0008, g32p_row03_traceSegment_073_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1181 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1181 17 17, g32p_row03_traceSegment_073_1181_0017, g32p_row03_traceSegment_073_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 1147 68 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1147 34 34, g32p_row03_traceSegment_073_1147_0034, g32p_row03_traceSegment_073_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 1080 135 = [15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1080 67 68, g32p_row03_traceSegment_073_1080_0067, g32p_row03_traceSegment_073_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 1215 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1231 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1231 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1231 8 9, g32p_row03_traceSegment_073_1231_0008, g32p_row03_traceSegment_073_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 1215 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1215 16 17, g32p_row03_traceSegment_073_1215_0016, g32p_row03_traceSegment_073_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1248 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1256 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1248 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1248 8 9, g32p_row03_traceSegment_073_1248_0008, g32p_row03_traceSegment_073_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1265 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1265 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1265 8 9, g32p_row03_traceSegment_073_1265_0008, g32p_row03_traceSegment_073_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1248 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1248 17 17, g32p_row03_traceSegment_073_1248_0017, g32p_row03_traceSegment_073_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 1215 67 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1215 33 34, g32p_row03_traceSegment_073_1215_0033, g32p_row03_traceSegment_073_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1282 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1282 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1282 8 9, g32p_row03_traceSegment_073_1282_0008, g32p_row03_traceSegment_073_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1299 8 9, g32p_row03_traceSegment_073_1299_0008, g32p_row03_traceSegment_073_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1282 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1282 17 17, g32p_row03_traceSegment_073_1282_0017, g32p_row03_traceSegment_073_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1324 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1316 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1316 8 9, g32p_row03_traceSegment_073_1316_0008, g32p_row03_traceSegment_073_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1333 8 9, g32p_row03_traceSegment_073_1333_0008, g32p_row03_traceSegment_073_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1316 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1316 17 17, g32p_row03_traceSegment_073_1316_0017, g32p_row03_traceSegment_073_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 1282 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1282 34 34, g32p_row03_traceSegment_073_1282_0034, g32p_row03_traceSegment_073_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 1215 135 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1215 67 68, g32p_row03_traceSegment_073_1215_0067, g32p_row03_traceSegment_073_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 1080 270 = [23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1080 135 135, g32p_row03_traceSegment_073_1080_0135, g32p_row03_traceSegment_073_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1366 8 9, g32p_row03_traceSegment_073_1366_0008, g32p_row03_traceSegment_073_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1350 16 17, g32p_row03_traceSegment_073_1350_0016, g32p_row03_traceSegment_073_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1383 8 9, g32p_row03_traceSegment_073_1383_0008, g32p_row03_traceSegment_073_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1400 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1400 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1400 8 9, g32p_row03_traceSegment_073_1400_0008, g32p_row03_traceSegment_073_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1383 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1383 17 17, g32p_row03_traceSegment_073_1383_0017, g32p_row03_traceSegment_073_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 1350 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1350 33 34, g32p_row03_traceSegment_073_1350_0033, g32p_row03_traceSegment_073_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1417 8 9, g32p_row03_traceSegment_073_1417_0008, g32p_row03_traceSegment_073_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1434 8 9, g32p_row03_traceSegment_073_1434_0008, g32p_row03_traceSegment_073_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1417 17 17, g32p_row03_traceSegment_073_1417_0017, g32p_row03_traceSegment_073_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1451 8 9, g32p_row03_traceSegment_073_1451_0008, g32p_row03_traceSegment_073_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1468 8 9, g32p_row03_traceSegment_073_1468_0008, g32p_row03_traceSegment_073_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1451 17 17, g32p_row03_traceSegment_073_1451_0017, g32p_row03_traceSegment_073_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1417 34 34, g32p_row03_traceSegment_073_1417_0034, g32p_row03_traceSegment_073_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 1350 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1350 67 68, g32p_row03_traceSegment_073_1350_0067, g32p_row03_traceSegment_073_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1501 8 9, g32p_row03_traceSegment_073_1501_0008, g32p_row03_traceSegment_073_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1485 16 17, g32p_row03_traceSegment_073_1485_0016, g32p_row03_traceSegment_073_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1518 8 9, g32p_row03_traceSegment_073_1518_0008, g32p_row03_traceSegment_073_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1543 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1535 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1535 8 9, g32p_row03_traceSegment_073_1535_0008, g32p_row03_traceSegment_073_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1518 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1518 17 17, g32p_row03_traceSegment_073_1518_0017, g32p_row03_traceSegment_073_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 1485 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1485 33 34, g32p_row03_traceSegment_073_1485_0033, g32p_row03_traceSegment_073_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1552 8 9, g32p_row03_traceSegment_073_1552_0008, g32p_row03_traceSegment_073_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1569 8 9, g32p_row03_traceSegment_073_1569_0008, g32p_row03_traceSegment_073_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1552 17 17, g32p_row03_traceSegment_073_1552_0017, g32p_row03_traceSegment_073_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1586 8 9, g32p_row03_traceSegment_073_1586_0008, g32p_row03_traceSegment_073_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1603 8 9, g32p_row03_traceSegment_073_1603_0008, g32p_row03_traceSegment_073_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1586 17 17, g32p_row03_traceSegment_073_1586_0017, g32p_row03_traceSegment_073_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1552 34 34, g32p_row03_traceSegment_073_1552_0034, g32p_row03_traceSegment_073_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 1485 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1485 67 68, g32p_row03_traceSegment_073_1485_0067, g32p_row03_traceSegment_073_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 1350 270 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1350 135 135, g32p_row03_traceSegment_073_1350_0135, g32p_row03_traceSegment_073_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_073 1080 540 = [25] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1080 270 270, g32p_row03_traceSegment_073_1080_0270, g32p_row03_traceSegment_073_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1636 8 9, g32p_row03_traceSegment_073_1636_0008, g32p_row03_traceSegment_073_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1620 16 17, g32p_row03_traceSegment_073_1620_0016, g32p_row03_traceSegment_073_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1653 8 9, g32p_row03_traceSegment_073_1653_0008, g32p_row03_traceSegment_073_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1670 8 9, g32p_row03_traceSegment_073_1670_0008, g32p_row03_traceSegment_073_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1653 17 17, g32p_row03_traceSegment_073_1653_0017, g32p_row03_traceSegment_073_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1620 33 34, g32p_row03_traceSegment_073_1620_0033, g32p_row03_traceSegment_073_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1687 8 9, g32p_row03_traceSegment_073_1687_0008, g32p_row03_traceSegment_073_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1704 8 9, g32p_row03_traceSegment_073_1704_0008, g32p_row03_traceSegment_073_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1687 17 17, g32p_row03_traceSegment_073_1687_0017, g32p_row03_traceSegment_073_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1721 8 9, g32p_row03_traceSegment_073_1721_0008, g32p_row03_traceSegment_073_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1738 8 9, g32p_row03_traceSegment_073_1738_0008, g32p_row03_traceSegment_073_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1721 17 17, g32p_row03_traceSegment_073_1721_0017, g32p_row03_traceSegment_073_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1687 34 34, g32p_row03_traceSegment_073_1687_0034, g32p_row03_traceSegment_073_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1620 67 68, g32p_row03_traceSegment_073_1620_0067, g32p_row03_traceSegment_073_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1771 8 9, g32p_row03_traceSegment_073_1771_0008, g32p_row03_traceSegment_073_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1755 16 17, g32p_row03_traceSegment_073_1755_0016, g32p_row03_traceSegment_073_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1788 8 9, g32p_row03_traceSegment_073_1788_0008, g32p_row03_traceSegment_073_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1805 8 9, g32p_row03_traceSegment_073_1805_0008, g32p_row03_traceSegment_073_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1788 17 17, g32p_row03_traceSegment_073_1788_0017, g32p_row03_traceSegment_073_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1755 33 34, g32p_row03_traceSegment_073_1755_0033, g32p_row03_traceSegment_073_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1822 8 9, g32p_row03_traceSegment_073_1822_0008, g32p_row03_traceSegment_073_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1839 8 9, g32p_row03_traceSegment_073_1839_0008, g32p_row03_traceSegment_073_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1822 17 17, g32p_row03_traceSegment_073_1822_0017, g32p_row03_traceSegment_073_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1856 8 9, g32p_row03_traceSegment_073_1856_0008, g32p_row03_traceSegment_073_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1873 8 9, g32p_row03_traceSegment_073_1873_0008, g32p_row03_traceSegment_073_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1856 17 17, g32p_row03_traceSegment_073_1856_0017, g32p_row03_traceSegment_073_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1822 34 34, g32p_row03_traceSegment_073_1822_0034, g32p_row03_traceSegment_073_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1755 67 68, g32p_row03_traceSegment_073_1755_0067, g32p_row03_traceSegment_073_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1620 135 135, g32p_row03_traceSegment_073_1620_0135, g32p_row03_traceSegment_073_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1906 8 9, g32p_row03_traceSegment_073_1906_0008, g32p_row03_traceSegment_073_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1890 16 17, g32p_row03_traceSegment_073_1890_0016, g32p_row03_traceSegment_073_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1923 8 9, g32p_row03_traceSegment_073_1923_0008, g32p_row03_traceSegment_073_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1940 8 9, g32p_row03_traceSegment_073_1940_0008, g32p_row03_traceSegment_073_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1923 17 17, g32p_row03_traceSegment_073_1923_0017, g32p_row03_traceSegment_073_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1890 33 34, g32p_row03_traceSegment_073_1890_0033, g32p_row03_traceSegment_073_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1957 8 9, g32p_row03_traceSegment_073_1957_0008, g32p_row03_traceSegment_073_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1974 8 9, g32p_row03_traceSegment_073_1974_0008, g32p_row03_traceSegment_073_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1957 17 17, g32p_row03_traceSegment_073_1957_0017, g32p_row03_traceSegment_073_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1991 8 9, g32p_row03_traceSegment_073_1991_0008, g32p_row03_traceSegment_073_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2008 8 9, g32p_row03_traceSegment_073_2008_0008, g32p_row03_traceSegment_073_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1991 17 17, g32p_row03_traceSegment_073_1991_0017, g32p_row03_traceSegment_073_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1957 34 34, g32p_row03_traceSegment_073_1957_0034, g32p_row03_traceSegment_073_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1890 67 68, g32p_row03_traceSegment_073_1890_0067, g32p_row03_traceSegment_073_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2041 8 9, g32p_row03_traceSegment_073_2041_0008, g32p_row03_traceSegment_073_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2025 16 17, g32p_row03_traceSegment_073_2025_0016, g32p_row03_traceSegment_073_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2058 8 9, g32p_row03_traceSegment_073_2058_0008, g32p_row03_traceSegment_073_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2075 8 9, g32p_row03_traceSegment_073_2075_0008, g32p_row03_traceSegment_073_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2058 17 17, g32p_row03_traceSegment_073_2058_0017, g32p_row03_traceSegment_073_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2025 33 34, g32p_row03_traceSegment_073_2025_0033, g32p_row03_traceSegment_073_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2092 8 9, g32p_row03_traceSegment_073_2092_0008, g32p_row03_traceSegment_073_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2109 8 9, g32p_row03_traceSegment_073_2109_0008, g32p_row03_traceSegment_073_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2092 17 17, g32p_row03_traceSegment_073_2092_0017, g32p_row03_traceSegment_073_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2134 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2126 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2126 8 9, g32p_row03_traceSegment_073_2126_0008, g32p_row03_traceSegment_073_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2143 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2143 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2143 8 9, g32p_row03_traceSegment_073_2143_0008, g32p_row03_traceSegment_073_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2126 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2126 17 17, g32p_row03_traceSegment_073_2126_0017, g32p_row03_traceSegment_073_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 2092 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2092 34 34, g32p_row03_traceSegment_073_2092_0034, g32p_row03_traceSegment_073_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 2025 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2025 67 68, g32p_row03_traceSegment_073_2025_0067, g32p_row03_traceSegment_073_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 1890 270 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1890 135 135, g32p_row03_traceSegment_073_1890_0135, g32p_row03_traceSegment_073_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_073 1620 540 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1620 270 270, g32p_row03_traceSegment_073_1620_0270, g32p_row03_traceSegment_073_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_073_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_073 1080 1080 = [28] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 1080 540 540, g32p_row03_traceSegment_073_1080_0540, g32p_row03_traceSegment_073_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_073 0 2160 = [63] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 0 1080 1080, g32p_row03_traceSegment_073_0000_1080, g32p_row03_traceSegment_073_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 2160 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2176 8 9, g32p_row03_traceSegment_073_2176_0008, g32p_row03_traceSegment_073_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 2160 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2160 16 17, g32p_row03_traceSegment_073_2160_0016, g32p_row03_traceSegment_073_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2193 8 9, g32p_row03_traceSegment_073_2193_0008, g32p_row03_traceSegment_073_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2210 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2210 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2210 8 9, g32p_row03_traceSegment_073_2210_0008, g32p_row03_traceSegment_073_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2193 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2193 17 17, g32p_row03_traceSegment_073_2193_0017, g32p_row03_traceSegment_073_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 2160 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2160 33 34, g32p_row03_traceSegment_073_2160_0033, g32p_row03_traceSegment_073_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2227 8 9, g32p_row03_traceSegment_073_2227_0008, g32p_row03_traceSegment_073_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2244 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2244 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2244 8 9, g32p_row03_traceSegment_073_2244_0008, g32p_row03_traceSegment_073_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2227 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2227 17 17, g32p_row03_traceSegment_073_2227_0017, g32p_row03_traceSegment_073_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2261 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2269 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2261 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2261 8 9, g32p_row03_traceSegment_073_2261_0008, g32p_row03_traceSegment_073_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2278 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2286 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2278 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2278 8 9, g32p_row03_traceSegment_073_2278_0008, g32p_row03_traceSegment_073_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2261 34 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2261 17 17, g32p_row03_traceSegment_073_2261_0017, g32p_row03_traceSegment_073_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 2227 68 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2227 34 34, g32p_row03_traceSegment_073_2227_0034, g32p_row03_traceSegment_073_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 2160 135 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2160 67 68, g32p_row03_traceSegment_073_2160_0067, g32p_row03_traceSegment_073_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2311 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2319 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2311 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2311 8 9, g32p_row03_traceSegment_073_2311_0008, g32p_row03_traceSegment_073_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 2295 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2295 16 17, g32p_row03_traceSegment_073_2295_0016, g32p_row03_traceSegment_073_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2336 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2328 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2328 8 9, g32p_row03_traceSegment_073_2328_0008, g32p_row03_traceSegment_073_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2345 8 9, g32p_row03_traceSegment_073_2345_0008, g32p_row03_traceSegment_073_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2328 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2328 17 17, g32p_row03_traceSegment_073_2328_0017, g32p_row03_traceSegment_073_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 2295 67 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2295 33 34, g32p_row03_traceSegment_073_2295_0033, g32p_row03_traceSegment_073_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2362 8 9, g32p_row03_traceSegment_073_2362_0008, g32p_row03_traceSegment_073_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2379 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2379 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2379 8 9, g32p_row03_traceSegment_073_2379_0008, g32p_row03_traceSegment_073_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2362 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2362 17 17, g32p_row03_traceSegment_073_2362_0017, g32p_row03_traceSegment_073_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2396 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2396 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2396 8 9, g32p_row03_traceSegment_073_2396_0008, g32p_row03_traceSegment_073_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2413 8 9, g32p_row03_traceSegment_073_2413_0008, g32p_row03_traceSegment_073_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2396 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2396 17 17, g32p_row03_traceSegment_073_2396_0017, g32p_row03_traceSegment_073_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 2362 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2362 34 34, g32p_row03_traceSegment_073_2362_0034, g32p_row03_traceSegment_073_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 2295 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2295 67 68, g32p_row03_traceSegment_073_2295_0067, g32p_row03_traceSegment_073_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 2160 270 = [14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2160 135 135, g32p_row03_traceSegment_073_2160_0135, g32p_row03_traceSegment_073_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2454 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2446 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2446 8 9, g32p_row03_traceSegment_073_2446_0008, g32p_row03_traceSegment_073_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 2430 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2430 16 17, g32p_row03_traceSegment_073_2430_0016, g32p_row03_traceSegment_073_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2471 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2463 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2463 8 9, g32p_row03_traceSegment_073_2463_0008, g32p_row03_traceSegment_073_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2488 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2480 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2480 8 9, g32p_row03_traceSegment_073_2480_0008, g32p_row03_traceSegment_073_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2463 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2463 17 17, g32p_row03_traceSegment_073_2463_0017, g32p_row03_traceSegment_073_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 2430 67 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2430 33 34, g32p_row03_traceSegment_073_2430_0033, g32p_row03_traceSegment_073_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2497 8 9, g32p_row03_traceSegment_073_2497_0008, g32p_row03_traceSegment_073_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2514 8 9, g32p_row03_traceSegment_073_2514_0008, g32p_row03_traceSegment_073_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2497 17 17, g32p_row03_traceSegment_073_2497_0017, g32p_row03_traceSegment_073_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2531 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2539 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2531 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2531 8 9, g32p_row03_traceSegment_073_2531_0008, g32p_row03_traceSegment_073_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2548 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2556 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2548 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2548 8 9, g32p_row03_traceSegment_073_2548_0008, g32p_row03_traceSegment_073_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2531 34 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2531 17 17, g32p_row03_traceSegment_073_2531_0017, g32p_row03_traceSegment_073_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 2497 68 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2497 34 34, g32p_row03_traceSegment_073_2497_0034, g32p_row03_traceSegment_073_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 2430 135 = [10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2430 67 68, g32p_row03_traceSegment_073_2430_0067, g32p_row03_traceSegment_073_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2581 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2589 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2581 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2581 8 9, g32p_row03_traceSegment_073_2581_0008, g32p_row03_traceSegment_073_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 2565 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2565 16 17, g32p_row03_traceSegment_073_2565_0016, g32p_row03_traceSegment_073_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2598 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2598 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2598 8 9, g32p_row03_traceSegment_073_2598_0008, g32p_row03_traceSegment_073_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2615 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2615 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2615 8 9, g32p_row03_traceSegment_073_2615_0008, g32p_row03_traceSegment_073_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2598 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2598 17 17, g32p_row03_traceSegment_073_2598_0017, g32p_row03_traceSegment_073_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 2565 67 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2565 33 34, g32p_row03_traceSegment_073_2565_0033, g32p_row03_traceSegment_073_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2640 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2632 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2632 8 9, g32p_row03_traceSegment_073_2632_0008, g32p_row03_traceSegment_073_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2657 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2649 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2649 8 9, g32p_row03_traceSegment_073_2649_0008, g32p_row03_traceSegment_073_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2632 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2632 17 17, g32p_row03_traceSegment_073_2632_0017, g32p_row03_traceSegment_073_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2674 9 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2666 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2666 8 9, g32p_row03_traceSegment_073_2666_0008, g32p_row03_traceSegment_073_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2683 8 9, g32p_row03_traceSegment_073_2683_0008, g32p_row03_traceSegment_073_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2666 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2666 17 17, g32p_row03_traceSegment_073_2666_0017, g32p_row03_traceSegment_073_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 2632 68 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2632 34 34, g32p_row03_traceSegment_073_2632_0034, g32p_row03_traceSegment_073_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 2565 135 = [9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2565 67 68, g32p_row03_traceSegment_073_2565_0067, g32p_row03_traceSegment_073_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 2430 270 = [19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2430 135 135, g32p_row03_traceSegment_073_2430_0135, g32p_row03_traceSegment_073_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_073 2160 540 = [33] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2160 270 270, g32p_row03_traceSegment_073_2160_0270, g32p_row03_traceSegment_073_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2716 8 9, g32p_row03_traceSegment_073_2716_0008, g32p_row03_traceSegment_073_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2700 16 17, g32p_row03_traceSegment_073_2700_0016, g32p_row03_traceSegment_073_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2741 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2733 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2733 8 9, g32p_row03_traceSegment_073_2733_0008, g32p_row03_traceSegment_073_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2750 8 9, g32p_row03_traceSegment_073_2750_0008, g32p_row03_traceSegment_073_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2733 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2733 17 17, g32p_row03_traceSegment_073_2733_0017, g32p_row03_traceSegment_073_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 2700 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2700 33 34, g32p_row03_traceSegment_073_2700_0033, g32p_row03_traceSegment_073_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2767 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2775 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2767 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2767 8 9, g32p_row03_traceSegment_073_2767_0008, g32p_row03_traceSegment_073_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2784 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2792 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2784 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2784 8 9, g32p_row03_traceSegment_073_2784_0008, g32p_row03_traceSegment_073_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2767 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2767 17 17, g32p_row03_traceSegment_073_2767_0017, g32p_row03_traceSegment_073_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2801 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2809 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2801 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2801 8 9, g32p_row03_traceSegment_073_2801_0008, g32p_row03_traceSegment_073_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2818 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2818 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2818 8 9, g32p_row03_traceSegment_073_2818_0008, g32p_row03_traceSegment_073_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2801 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2801 17 17, g32p_row03_traceSegment_073_2801_0017, g32p_row03_traceSegment_073_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 2767 68 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2767 34 34, g32p_row03_traceSegment_073_2767_0034, g32p_row03_traceSegment_073_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 2700 135 = [9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2700 67 68, g32p_row03_traceSegment_073_2700_0067, g32p_row03_traceSegment_073_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 2835 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2859 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2851 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2851 8 9, g32p_row03_traceSegment_073_2851_0008, g32p_row03_traceSegment_073_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 2835 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2835 16 17, g32p_row03_traceSegment_073_2835_0016, g32p_row03_traceSegment_073_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2868 8 9, g32p_row03_traceSegment_073_2868_0008, g32p_row03_traceSegment_073_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2885 8 9, g32p_row03_traceSegment_073_2885_0008, g32p_row03_traceSegment_073_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2868 17 17, g32p_row03_traceSegment_073_2868_0017, g32p_row03_traceSegment_073_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 2835 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2835 33 34, g32p_row03_traceSegment_073_2835_0033, g32p_row03_traceSegment_073_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2902 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2910 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2902 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2902 8 9, g32p_row03_traceSegment_073_2902_0008, g32p_row03_traceSegment_073_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2919 8 9, g32p_row03_traceSegment_073_2919_0008, g32p_row03_traceSegment_073_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2902 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2902 17 17, g32p_row03_traceSegment_073_2902_0017, g32p_row03_traceSegment_073_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2936 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2936 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2936 8 9, g32p_row03_traceSegment_073_2936_0008, g32p_row03_traceSegment_073_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2961 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2953 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2953 8 9, g32p_row03_traceSegment_073_2953_0008, g32p_row03_traceSegment_073_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 2936 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2936 17 17, g32p_row03_traceSegment_073_2936_0017, g32p_row03_traceSegment_073_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 2902 68 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2902 34 34, g32p_row03_traceSegment_073_2902_0034, g32p_row03_traceSegment_073_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 2835 135 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2835 67 68, g32p_row03_traceSegment_073_2835_0067, g32p_row03_traceSegment_073_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 2700 270 = [17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2700 135 135, g32p_row03_traceSegment_073_2700_0135, g32p_row03_traceSegment_073_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 2970 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 2994 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 2986 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2986 8 9, g32p_row03_traceSegment_073_2986_0008, g32p_row03_traceSegment_073_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 2970 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2970 16 17, g32p_row03_traceSegment_073_2970_0016, g32p_row03_traceSegment_073_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3003 8 9, g32p_row03_traceSegment_073_3003_0008, g32p_row03_traceSegment_073_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3028 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3020 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3020 8 9, g32p_row03_traceSegment_073_3020_0008, g32p_row03_traceSegment_073_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3003 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3003 17 17, g32p_row03_traceSegment_073_3003_0017, g32p_row03_traceSegment_073_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 2970 67 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2970 33 34, g32p_row03_traceSegment_073_2970_0033, g32p_row03_traceSegment_073_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3037 8 9, g32p_row03_traceSegment_073_3037_0008, g32p_row03_traceSegment_073_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3054 8 9, g32p_row03_traceSegment_073_3054_0008, g32p_row03_traceSegment_073_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3037 17 17, g32p_row03_traceSegment_073_3037_0017, g32p_row03_traceSegment_073_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3071 8 9, g32p_row03_traceSegment_073_3071_0008, g32p_row03_traceSegment_073_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3088 8 9, g32p_row03_traceSegment_073_3088_0008, g32p_row03_traceSegment_073_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3071 17 17, g32p_row03_traceSegment_073_3071_0017, g32p_row03_traceSegment_073_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3037 34 34, g32p_row03_traceSegment_073_3037_0034, g32p_row03_traceSegment_073_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 2970 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2970 67 68, g32p_row03_traceSegment_073_2970_0067, g32p_row03_traceSegment_073_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3121 8 9, g32p_row03_traceSegment_073_3121_0008, g32p_row03_traceSegment_073_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3105 16 17, g32p_row03_traceSegment_073_3105_0016, g32p_row03_traceSegment_073_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3138 8 9, g32p_row03_traceSegment_073_3138_0008, g32p_row03_traceSegment_073_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3155 8 9, g32p_row03_traceSegment_073_3155_0008, g32p_row03_traceSegment_073_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3138 17 17, g32p_row03_traceSegment_073_3138_0017, g32p_row03_traceSegment_073_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3105 33 34, g32p_row03_traceSegment_073_3105_0033, g32p_row03_traceSegment_073_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3172 8 9, g32p_row03_traceSegment_073_3172_0008, g32p_row03_traceSegment_073_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3189 8 9, g32p_row03_traceSegment_073_3189_0008, g32p_row03_traceSegment_073_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3172 17 17, g32p_row03_traceSegment_073_3172_0017, g32p_row03_traceSegment_073_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3206 8 9, g32p_row03_traceSegment_073_3206_0008, g32p_row03_traceSegment_073_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3223 8 9, g32p_row03_traceSegment_073_3223_0008, g32p_row03_traceSegment_073_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3206 17 17, g32p_row03_traceSegment_073_3206_0017, g32p_row03_traceSegment_073_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3172 34 34, g32p_row03_traceSegment_073_3172_0034, g32p_row03_traceSegment_073_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3105 67 68, g32p_row03_traceSegment_073_3105_0067, g32p_row03_traceSegment_073_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 2970 270 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2970 135 135, g32p_row03_traceSegment_073_2970_0135, g32p_row03_traceSegment_073_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_073 2700 540 = [21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2700 270 270, g32p_row03_traceSegment_073_2700_0270, g32p_row03_traceSegment_073_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_073 2160 1080 = [54] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2160 540 540, g32p_row03_traceSegment_073_2160_0540, g32p_row03_traceSegment_073_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3256 8 9, g32p_row03_traceSegment_073_3256_0008, g32p_row03_traceSegment_073_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3240 16 17, g32p_row03_traceSegment_073_3240_0016, g32p_row03_traceSegment_073_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3273 8 9, g32p_row03_traceSegment_073_3273_0008, g32p_row03_traceSegment_073_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3290 8 9, g32p_row03_traceSegment_073_3290_0008, g32p_row03_traceSegment_073_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3273 17 17, g32p_row03_traceSegment_073_3273_0017, g32p_row03_traceSegment_073_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3240 33 34, g32p_row03_traceSegment_073_3240_0033, g32p_row03_traceSegment_073_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3307 8 9, g32p_row03_traceSegment_073_3307_0008, g32p_row03_traceSegment_073_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3324 8 9, g32p_row03_traceSegment_073_3324_0008, g32p_row03_traceSegment_073_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3307 17 17, g32p_row03_traceSegment_073_3307_0017, g32p_row03_traceSegment_073_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3341 8 9, g32p_row03_traceSegment_073_3341_0008, g32p_row03_traceSegment_073_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3358 8 9, g32p_row03_traceSegment_073_3358_0008, g32p_row03_traceSegment_073_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3341 17 17, g32p_row03_traceSegment_073_3341_0017, g32p_row03_traceSegment_073_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3307 34 34, g32p_row03_traceSegment_073_3307_0034, g32p_row03_traceSegment_073_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3240 67 68, g32p_row03_traceSegment_073_3240_0067, g32p_row03_traceSegment_073_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3391 8 9, g32p_row03_traceSegment_073_3391_0008, g32p_row03_traceSegment_073_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3375 16 17, g32p_row03_traceSegment_073_3375_0016, g32p_row03_traceSegment_073_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3408 8 9, g32p_row03_traceSegment_073_3408_0008, g32p_row03_traceSegment_073_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3425 8 9, g32p_row03_traceSegment_073_3425_0008, g32p_row03_traceSegment_073_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3408 17 17, g32p_row03_traceSegment_073_3408_0017, g32p_row03_traceSegment_073_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3375 33 34, g32p_row03_traceSegment_073_3375_0033, g32p_row03_traceSegment_073_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3450 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3442 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3442 8 9, g32p_row03_traceSegment_073_3442_0008, g32p_row03_traceSegment_073_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3459 8 9, g32p_row03_traceSegment_073_3459_0008, g32p_row03_traceSegment_073_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3442 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3442 17 17, g32p_row03_traceSegment_073_3442_0017, g32p_row03_traceSegment_073_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3476 8 9, g32p_row03_traceSegment_073_3476_0008, g32p_row03_traceSegment_073_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3493 8 9, g32p_row03_traceSegment_073_3493_0008, g32p_row03_traceSegment_073_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3476 17 17, g32p_row03_traceSegment_073_3476_0017, g32p_row03_traceSegment_073_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 3442 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3442 34 34, g32p_row03_traceSegment_073_3442_0034, g32p_row03_traceSegment_073_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 3375 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3375 67 68, g32p_row03_traceSegment_073_3375_0067, g32p_row03_traceSegment_073_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 3240 270 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3240 135 135, g32p_row03_traceSegment_073_3240_0135, g32p_row03_traceSegment_073_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3526 8 9, g32p_row03_traceSegment_073_3526_0008, g32p_row03_traceSegment_073_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3510 16 17, g32p_row03_traceSegment_073_3510_0016, g32p_row03_traceSegment_073_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3543 8 9, g32p_row03_traceSegment_073_3543_0008, g32p_row03_traceSegment_073_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3560 8 9, g32p_row03_traceSegment_073_3560_0008, g32p_row03_traceSegment_073_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3543 17 17, g32p_row03_traceSegment_073_3543_0017, g32p_row03_traceSegment_073_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3510 33 34, g32p_row03_traceSegment_073_3510_0033, g32p_row03_traceSegment_073_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3577 8 9, g32p_row03_traceSegment_073_3577_0008, g32p_row03_traceSegment_073_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3594 8 9, g32p_row03_traceSegment_073_3594_0008, g32p_row03_traceSegment_073_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3577 17 17, g32p_row03_traceSegment_073_3577_0017, g32p_row03_traceSegment_073_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3619 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3611 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3611 8 9, g32p_row03_traceSegment_073_3611_0008, g32p_row03_traceSegment_073_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3628 8 9, g32p_row03_traceSegment_073_3628_0008, g32p_row03_traceSegment_073_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3611 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3611 17 17, g32p_row03_traceSegment_073_3611_0017, g32p_row03_traceSegment_073_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 3577 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3577 34 34, g32p_row03_traceSegment_073_3577_0034, g32p_row03_traceSegment_073_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 3510 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3510 67 68, g32p_row03_traceSegment_073_3510_0067, g32p_row03_traceSegment_073_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3661 8 9, g32p_row03_traceSegment_073_3661_0008, g32p_row03_traceSegment_073_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3645 16 17, g32p_row03_traceSegment_073_3645_0016, g32p_row03_traceSegment_073_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3678 8 9, g32p_row03_traceSegment_073_3678_0008, g32p_row03_traceSegment_073_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3695 8 9, g32p_row03_traceSegment_073_3695_0008, g32p_row03_traceSegment_073_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3678 17 17, g32p_row03_traceSegment_073_3678_0017, g32p_row03_traceSegment_073_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3645 33 34, g32p_row03_traceSegment_073_3645_0033, g32p_row03_traceSegment_073_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3712 8 9, g32p_row03_traceSegment_073_3712_0008, g32p_row03_traceSegment_073_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3737 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3729 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3729 8 9, g32p_row03_traceSegment_073_3729_0008, g32p_row03_traceSegment_073_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3712 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3712 17 17, g32p_row03_traceSegment_073_3712_0017, g32p_row03_traceSegment_073_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3746 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3746 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3746 8 9, g32p_row03_traceSegment_073_3746_0008, g32p_row03_traceSegment_073_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3763 8 9, g32p_row03_traceSegment_073_3763_0008, g32p_row03_traceSegment_073_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3746 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3746 17 17, g32p_row03_traceSegment_073_3746_0017, g32p_row03_traceSegment_073_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 3712 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3712 34 34, g32p_row03_traceSegment_073_3712_0034, g32p_row03_traceSegment_073_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 3645 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3645 67 68, g32p_row03_traceSegment_073_3645_0067, g32p_row03_traceSegment_073_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 3510 270 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3510 135 135, g32p_row03_traceSegment_073_3510_0135, g32p_row03_traceSegment_073_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_073 3240 540 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3240 270 270, g32p_row03_traceSegment_073_3240_0270, g32p_row03_traceSegment_073_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 3780 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3804 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3796 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3796 8 9, g32p_row03_traceSegment_073_3796_0008, g32p_row03_traceSegment_073_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 3780 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3780 16 17, g32p_row03_traceSegment_073_3780_0016, g32p_row03_traceSegment_073_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3821 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3813 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3813 8 9, g32p_row03_traceSegment_073_3813_0008, g32p_row03_traceSegment_073_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3830 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3830 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3830 8 9, g32p_row03_traceSegment_073_3830_0008, g32p_row03_traceSegment_073_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3813 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3813 17 17, g32p_row03_traceSegment_073_3813_0017, g32p_row03_traceSegment_073_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 3780 67 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3780 33 34, g32p_row03_traceSegment_073_3780_0033, g32p_row03_traceSegment_073_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3847 8 9, g32p_row03_traceSegment_073_3847_0008, g32p_row03_traceSegment_073_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3864 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3864 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3864 8 9, g32p_row03_traceSegment_073_3864_0008, g32p_row03_traceSegment_073_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3847 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3847 17 17, g32p_row03_traceSegment_073_3847_0017, g32p_row03_traceSegment_073_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3889 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3881 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3881 8 9, g32p_row03_traceSegment_073_3881_0008, g32p_row03_traceSegment_073_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3906 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3898 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3898 8 9, g32p_row03_traceSegment_073_3898_0008, g32p_row03_traceSegment_073_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3881 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3881 17 17, g32p_row03_traceSegment_073_3881_0017, g32p_row03_traceSegment_073_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 3847 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3847 34 34, g32p_row03_traceSegment_073_3847_0034, g32p_row03_traceSegment_073_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 3780 135 = [10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3780 67 68, g32p_row03_traceSegment_073_3780_0067, g32p_row03_traceSegment_073_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 3915 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3931 8 9, g32p_row03_traceSegment_073_3931_0008, g32p_row03_traceSegment_073_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 3915 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3915 16 17, g32p_row03_traceSegment_073_3915_0016, g32p_row03_traceSegment_073_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3948 8 9, g32p_row03_traceSegment_073_3948_0008, g32p_row03_traceSegment_073_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3973 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3965 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3965 8 9, g32p_row03_traceSegment_073_3965_0008, g32p_row03_traceSegment_073_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3948 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3948 17 17, g32p_row03_traceSegment_073_3948_0017, g32p_row03_traceSegment_073_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 3915 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3915 33 34, g32p_row03_traceSegment_073_3915_0033, g32p_row03_traceSegment_073_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3982 8 9, g32p_row03_traceSegment_073_3982_0008, g32p_row03_traceSegment_073_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3999 8 9, g32p_row03_traceSegment_073_3999_0008, g32p_row03_traceSegment_073_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3982 17 17, g32p_row03_traceSegment_073_3982_0017, g32p_row03_traceSegment_073_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4016 8 9, g32p_row03_traceSegment_073_4016_0008, g32p_row03_traceSegment_073_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4033 8 9, g32p_row03_traceSegment_073_4033_0008, g32p_row03_traceSegment_073_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4016 17 17, g32p_row03_traceSegment_073_4016_0017, g32p_row03_traceSegment_073_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3982 34 34, g32p_row03_traceSegment_073_3982_0034, g32p_row03_traceSegment_073_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 3915 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3915 67 68, g32p_row03_traceSegment_073_3915_0067, g32p_row03_traceSegment_073_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 3780 270 = [12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3780 135 135, g32p_row03_traceSegment_073_3780_0135, g32p_row03_traceSegment_073_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 4050 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4066 8 9, g32p_row03_traceSegment_073_4066_0008, g32p_row03_traceSegment_073_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 4050 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4050 16 17, g32p_row03_traceSegment_073_4050_0016, g32p_row03_traceSegment_073_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4083 8 9, g32p_row03_traceSegment_073_4083_0008, g32p_row03_traceSegment_073_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4108 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4100 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4100 8 9, g32p_row03_traceSegment_073_4100_0008, g32p_row03_traceSegment_073_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 4083 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4083 17 17, g32p_row03_traceSegment_073_4083_0017, g32p_row03_traceSegment_073_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 4050 67 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4050 33 34, g32p_row03_traceSegment_073_4050_0033, g32p_row03_traceSegment_073_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4125 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4117 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4117 8 9, g32p_row03_traceSegment_073_4117_0008, g32p_row03_traceSegment_073_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4134 8 9, g32p_row03_traceSegment_073_4134_0008, g32p_row03_traceSegment_073_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 4117 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4117 17 17, g32p_row03_traceSegment_073_4117_0017, g32p_row03_traceSegment_073_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4151 8 9, g32p_row03_traceSegment_073_4151_0008, g32p_row03_traceSegment_073_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4168 8 9, g32p_row03_traceSegment_073_4168_0008, g32p_row03_traceSegment_073_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4151 17 17, g32p_row03_traceSegment_073_4151_0017, g32p_row03_traceSegment_073_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 4117 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4117 34 34, g32p_row03_traceSegment_073_4117_0034, g32p_row03_traceSegment_073_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 4050 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4050 67 68, g32p_row03_traceSegment_073_4050_0067, g32p_row03_traceSegment_073_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_073 4185 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4201 8 9, g32p_row03_traceSegment_073_4201_0008, g32p_row03_traceSegment_073_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_073 4185 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4185 16 17, g32p_row03_traceSegment_073_4185_0016, g32p_row03_traceSegment_073_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4218 8 9, g32p_row03_traceSegment_073_4218_0008, g32p_row03_traceSegment_073_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4235 8 9, g32p_row03_traceSegment_073_4235_0008, g32p_row03_traceSegment_073_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4218 17 17, g32p_row03_traceSegment_073_4218_0017, g32p_row03_traceSegment_073_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_073 4185 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4185 33 34, g32p_row03_traceSegment_073_4185_0033, g32p_row03_traceSegment_073_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4260 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4252 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4252 8 9, g32p_row03_traceSegment_073_4252_0008, g32p_row03_traceSegment_073_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4269 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4269 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4269 8 9, g32p_row03_traceSegment_073_4269_0008, g32p_row03_traceSegment_073_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 4252 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4252 17 17, g32p_row03_traceSegment_073_4252_0017, g32p_row03_traceSegment_073_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4286 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4286 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4286 8 9, g32p_row03_traceSegment_073_4286_0008, g32p_row03_traceSegment_073_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_073 4303 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_073 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_073_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_073 4303 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4303 8 9, g32p_row03_traceSegment_073_4303_0008, g32p_row03_traceSegment_073_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_073 4286 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4286 17 17, g32p_row03_traceSegment_073_4286_0017, g32p_row03_traceSegment_073_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_073 4252 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4252 34 34, g32p_row03_traceSegment_073_4252_0034, g32p_row03_traceSegment_073_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_073 4185 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4185 67 68, g32p_row03_traceSegment_073_4185_0067, g32p_row03_traceSegment_073_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_073_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_073 4050 270 = [10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 4050 135 135, g32p_row03_traceSegment_073_4050_0135, g32p_row03_traceSegment_073_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_073 3780 540 = [22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3780 270 270, g32p_row03_traceSegment_073_3780_0270, g32p_row03_traceSegment_073_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_073_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_073 3240 1080 = [27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 3240 540 540, g32p_row03_traceSegment_073_3240_0540, g32p_row03_traceSegment_073_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_073_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_073 2160 2160 = [81] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 2160 1080 1080, g32p_row03_traceSegment_073_2160_1080, g32p_row03_traceSegment_073_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_073_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_073 0 4320 = [144] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_073 0 2160 2160, g32p_row03_traceSegment_073_0000_2160, g32p_row03_traceSegment_073_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_073 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 73 = [144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_073_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 56) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 56) (g32p_literalTraceValue 2 56)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_056]
  decide +kernel

theorem g32p_row03_tracePolynomial_057 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 57) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 57) (g32p_literalTraceValue 2 57)
      [1, -1, 1] [0, 4320, 4320] = true := by
  rw [g32p_row03_traceCoefficients_057]
  decide +kernel

theorem g32p_row03_tracePolynomial_060 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 60) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 60) (g32p_literalTraceValue 2 60)
      [1, -1, 1] [4320, 4320, 4320] = true := by
  rw [g32p_row03_traceCoefficients_060]
  decide +kernel

theorem g32p_row03_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 65) (g32p_literalTraceValue 2 65)
      [1, -1, 1] [-51840] = true := by
  rw [g32p_row03_traceCoefficients_065]
  decide +kernel

theorem g32p_row03_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 66) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 66) (g32p_literalTraceValue 2 66)
      [1, -1, 1] [-12960] = true := by
  rw [g32p_row03_traceCoefficients_066]
  decide +kernel

theorem g32p_row03_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 69) (g32p_literalTraceValue 2 69)
      [1, -1, 1] [8640, 8640] = true := by
  rw [g32p_row03_traceCoefficients_069]
  decide +kernel

theorem g32p_row03_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 71) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 71) (g32p_literalTraceValue 2 71)
      [1, -1, 1] [12960, 12960] = true := by
  rw [g32p_row03_traceCoefficients_071]
  decide +kernel

theorem g32p_row03_tracePolynomial_073 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 73) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 73) (g32p_literalTraceValue 2 73)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_073]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
