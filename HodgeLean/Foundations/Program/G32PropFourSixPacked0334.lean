import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0317
import HodgeLean.Foundations.Program.G32PropFourSixPacked0321
import HodgeLean.Foundations.Program.G32PropFourSixPacked0325
import HodgeLean.Foundations.Program.G32PropFourSixPacked0329
import HodgeLean.Foundations.Program.G32PropFourSixPacked0333
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_099_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 0 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 16 8 9, g32p_row03_traceSegment_099_0016_0008, g32p_row03_traceSegment_099_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 0 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 0 16 17, g32p_row03_traceSegment_099_0000_0016, g32p_row03_traceSegment_099_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 33 8 9, g32p_row03_traceSegment_099_0033_0008, g32p_row03_traceSegment_099_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 50 8 9, g32p_row03_traceSegment_099_0050_0008, g32p_row03_traceSegment_099_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 33 17 17, g32p_row03_traceSegment_099_0033_0017, g32p_row03_traceSegment_099_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 0 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 0 33 34, g32p_row03_traceSegment_099_0000_0033, g32p_row03_traceSegment_099_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 67 8 9, g32p_row03_traceSegment_099_0067_0008, g32p_row03_traceSegment_099_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 84 8 9, g32p_row03_traceSegment_099_0084_0008, g32p_row03_traceSegment_099_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 67 17 17, g32p_row03_traceSegment_099_0067_0017, g32p_row03_traceSegment_099_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 101 8 9, g32p_row03_traceSegment_099_0101_0008, g32p_row03_traceSegment_099_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 118 8 9, g32p_row03_traceSegment_099_0118_0008, g32p_row03_traceSegment_099_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 101 17 17, g32p_row03_traceSegment_099_0101_0017, g32p_row03_traceSegment_099_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 67 34 34, g32p_row03_traceSegment_099_0067_0034, g32p_row03_traceSegment_099_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 0 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 0 67 68, g32p_row03_traceSegment_099_0000_0067, g32p_row03_traceSegment_099_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 151 8 9, g32p_row03_traceSegment_099_0151_0008, g32p_row03_traceSegment_099_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 135 16 17, g32p_row03_traceSegment_099_0135_0016, g32p_row03_traceSegment_099_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 168 8 9, g32p_row03_traceSegment_099_0168_0008, g32p_row03_traceSegment_099_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 185 8 9, g32p_row03_traceSegment_099_0185_0008, g32p_row03_traceSegment_099_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 168 17 17, g32p_row03_traceSegment_099_0168_0017, g32p_row03_traceSegment_099_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 135 33 34, g32p_row03_traceSegment_099_0135_0033, g32p_row03_traceSegment_099_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 202 8 9, g32p_row03_traceSegment_099_0202_0008, g32p_row03_traceSegment_099_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 219 8 9, g32p_row03_traceSegment_099_0219_0008, g32p_row03_traceSegment_099_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 202 17 17, g32p_row03_traceSegment_099_0202_0017, g32p_row03_traceSegment_099_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 236 8 9, g32p_row03_traceSegment_099_0236_0008, g32p_row03_traceSegment_099_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 253 8 9, g32p_row03_traceSegment_099_0253_0008, g32p_row03_traceSegment_099_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 236 17 17, g32p_row03_traceSegment_099_0236_0017, g32p_row03_traceSegment_099_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 202 34 34, g32p_row03_traceSegment_099_0202_0034, g32p_row03_traceSegment_099_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 135 67 68, g32p_row03_traceSegment_099_0135_0067, g32p_row03_traceSegment_099_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 0 270 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 0 135 135, g32p_row03_traceSegment_099_0000_0135, g32p_row03_traceSegment_099_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 286 8 9, g32p_row03_traceSegment_099_0286_0008, g32p_row03_traceSegment_099_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 270 16 17, g32p_row03_traceSegment_099_0270_0016, g32p_row03_traceSegment_099_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 303 8 9, g32p_row03_traceSegment_099_0303_0008, g32p_row03_traceSegment_099_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 320 8 9, g32p_row03_traceSegment_099_0320_0008, g32p_row03_traceSegment_099_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 303 17 17, g32p_row03_traceSegment_099_0303_0017, g32p_row03_traceSegment_099_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 270 33 34, g32p_row03_traceSegment_099_0270_0033, g32p_row03_traceSegment_099_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 337 8 9, g32p_row03_traceSegment_099_0337_0008, g32p_row03_traceSegment_099_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 354 8 9, g32p_row03_traceSegment_099_0354_0008, g32p_row03_traceSegment_099_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 337 17 17, g32p_row03_traceSegment_099_0337_0017, g32p_row03_traceSegment_099_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 371 8 9, g32p_row03_traceSegment_099_0371_0008, g32p_row03_traceSegment_099_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 388 8 9, g32p_row03_traceSegment_099_0388_0008, g32p_row03_traceSegment_099_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 371 17 17, g32p_row03_traceSegment_099_0371_0017, g32p_row03_traceSegment_099_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 337 34 34, g32p_row03_traceSegment_099_0337_0034, g32p_row03_traceSegment_099_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 270 67 68, g32p_row03_traceSegment_099_0270_0067, g32p_row03_traceSegment_099_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 421 8 9, g32p_row03_traceSegment_099_0421_0008, g32p_row03_traceSegment_099_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 405 16 17, g32p_row03_traceSegment_099_0405_0016, g32p_row03_traceSegment_099_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 438 8 9, g32p_row03_traceSegment_099_0438_0008, g32p_row03_traceSegment_099_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 455 8 9, g32p_row03_traceSegment_099_0455_0008, g32p_row03_traceSegment_099_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 438 17 17, g32p_row03_traceSegment_099_0438_0017, g32p_row03_traceSegment_099_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 405 33 34, g32p_row03_traceSegment_099_0405_0033, g32p_row03_traceSegment_099_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 472 8 9, g32p_row03_traceSegment_099_0472_0008, g32p_row03_traceSegment_099_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 489 8 9, g32p_row03_traceSegment_099_0489_0008, g32p_row03_traceSegment_099_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 472 17 17, g32p_row03_traceSegment_099_0472_0017, g32p_row03_traceSegment_099_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 506 8 9, g32p_row03_traceSegment_099_0506_0008, g32p_row03_traceSegment_099_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 523 8 9, g32p_row03_traceSegment_099_0523_0008, g32p_row03_traceSegment_099_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 506 17 17, g32p_row03_traceSegment_099_0506_0017, g32p_row03_traceSegment_099_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 472 34 34, g32p_row03_traceSegment_099_0472_0034, g32p_row03_traceSegment_099_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 405 67 68, g32p_row03_traceSegment_099_0405_0067, g32p_row03_traceSegment_099_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 270 135 135, g32p_row03_traceSegment_099_0270_0135, g32p_row03_traceSegment_099_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_099 0 540 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 0 270 270, g32p_row03_traceSegment_099_0000_0270, g32p_row03_traceSegment_099_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 556 8 9, g32p_row03_traceSegment_099_0556_0008, g32p_row03_traceSegment_099_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 540 16 17, g32p_row03_traceSegment_099_0540_0016, g32p_row03_traceSegment_099_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 573 8 9, g32p_row03_traceSegment_099_0573_0008, g32p_row03_traceSegment_099_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 590 8 9, g32p_row03_traceSegment_099_0590_0008, g32p_row03_traceSegment_099_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 573 17 17, g32p_row03_traceSegment_099_0573_0017, g32p_row03_traceSegment_099_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 540 33 34, g32p_row03_traceSegment_099_0540_0033, g32p_row03_traceSegment_099_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 607 8 9, g32p_row03_traceSegment_099_0607_0008, g32p_row03_traceSegment_099_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 624 8 9, g32p_row03_traceSegment_099_0624_0008, g32p_row03_traceSegment_099_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 607 17 17, g32p_row03_traceSegment_099_0607_0017, g32p_row03_traceSegment_099_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 641 8 9, g32p_row03_traceSegment_099_0641_0008, g32p_row03_traceSegment_099_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 658 8 9, g32p_row03_traceSegment_099_0658_0008, g32p_row03_traceSegment_099_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 641 17 17, g32p_row03_traceSegment_099_0641_0017, g32p_row03_traceSegment_099_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 607 34 34, g32p_row03_traceSegment_099_0607_0034, g32p_row03_traceSegment_099_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 540 67 68, g32p_row03_traceSegment_099_0540_0067, g32p_row03_traceSegment_099_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 691 8 9, g32p_row03_traceSegment_099_0691_0008, g32p_row03_traceSegment_099_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 675 16 17, g32p_row03_traceSegment_099_0675_0016, g32p_row03_traceSegment_099_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 708 8 9, g32p_row03_traceSegment_099_0708_0008, g32p_row03_traceSegment_099_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 725 8 9, g32p_row03_traceSegment_099_0725_0008, g32p_row03_traceSegment_099_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 708 17 17, g32p_row03_traceSegment_099_0708_0017, g32p_row03_traceSegment_099_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 675 33 34, g32p_row03_traceSegment_099_0675_0033, g32p_row03_traceSegment_099_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 742 8 9, g32p_row03_traceSegment_099_0742_0008, g32p_row03_traceSegment_099_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 759 8 9, g32p_row03_traceSegment_099_0759_0008, g32p_row03_traceSegment_099_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 742 17 17, g32p_row03_traceSegment_099_0742_0017, g32p_row03_traceSegment_099_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 776 8 9, g32p_row03_traceSegment_099_0776_0008, g32p_row03_traceSegment_099_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 793 8 9, g32p_row03_traceSegment_099_0793_0008, g32p_row03_traceSegment_099_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 776 17 17, g32p_row03_traceSegment_099_0776_0017, g32p_row03_traceSegment_099_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 742 34 34, g32p_row03_traceSegment_099_0742_0034, g32p_row03_traceSegment_099_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 675 67 68, g32p_row03_traceSegment_099_0675_0067, g32p_row03_traceSegment_099_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 540 135 135, g32p_row03_traceSegment_099_0540_0135, g32p_row03_traceSegment_099_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 826 8 9, g32p_row03_traceSegment_099_0826_0008, g32p_row03_traceSegment_099_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 810 16 17, g32p_row03_traceSegment_099_0810_0016, g32p_row03_traceSegment_099_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 843 8 9, g32p_row03_traceSegment_099_0843_0008, g32p_row03_traceSegment_099_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 860 8 9, g32p_row03_traceSegment_099_0860_0008, g32p_row03_traceSegment_099_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 843 17 17, g32p_row03_traceSegment_099_0843_0017, g32p_row03_traceSegment_099_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 810 33 34, g32p_row03_traceSegment_099_0810_0033, g32p_row03_traceSegment_099_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 877 8 9, g32p_row03_traceSegment_099_0877_0008, g32p_row03_traceSegment_099_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 894 8 9, g32p_row03_traceSegment_099_0894_0008, g32p_row03_traceSegment_099_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 877 17 17, g32p_row03_traceSegment_099_0877_0017, g32p_row03_traceSegment_099_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 911 8 9, g32p_row03_traceSegment_099_0911_0008, g32p_row03_traceSegment_099_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 928 8 9, g32p_row03_traceSegment_099_0928_0008, g32p_row03_traceSegment_099_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 911 17 17, g32p_row03_traceSegment_099_0911_0017, g32p_row03_traceSegment_099_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 877 34 34, g32p_row03_traceSegment_099_0877_0034, g32p_row03_traceSegment_099_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 810 67 68, g32p_row03_traceSegment_099_0810_0067, g32p_row03_traceSegment_099_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 961 8 9, g32p_row03_traceSegment_099_0961_0008, g32p_row03_traceSegment_099_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 945 16 17, g32p_row03_traceSegment_099_0945_0016, g32p_row03_traceSegment_099_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 978 8 9, g32p_row03_traceSegment_099_0978_0008, g32p_row03_traceSegment_099_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 995 8 9, g32p_row03_traceSegment_099_0995_0008, g32p_row03_traceSegment_099_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 978 17 17, g32p_row03_traceSegment_099_0978_0017, g32p_row03_traceSegment_099_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 945 33 34, g32p_row03_traceSegment_099_0945_0033, g32p_row03_traceSegment_099_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1012 8 9, g32p_row03_traceSegment_099_1012_0008, g32p_row03_traceSegment_099_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1029 8 9, g32p_row03_traceSegment_099_1029_0008, g32p_row03_traceSegment_099_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1012 17 17, g32p_row03_traceSegment_099_1012_0017, g32p_row03_traceSegment_099_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1046 8 9, g32p_row03_traceSegment_099_1046_0008, g32p_row03_traceSegment_099_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1063 8 9, g32p_row03_traceSegment_099_1063_0008, g32p_row03_traceSegment_099_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1046 17 17, g32p_row03_traceSegment_099_1046_0017, g32p_row03_traceSegment_099_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1012 34 34, g32p_row03_traceSegment_099_1012_0034, g32p_row03_traceSegment_099_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 945 67 68, g32p_row03_traceSegment_099_0945_0067, g32p_row03_traceSegment_099_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 810 135 135, g32p_row03_traceSegment_099_0810_0135, g32p_row03_traceSegment_099_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_099 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 540 270 270, g32p_row03_traceSegment_099_0540_0270, g32p_row03_traceSegment_099_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_099 0 1080 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 0 540 540, g32p_row03_traceSegment_099_0000_0540, g32p_row03_traceSegment_099_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1096 8 9, g32p_row03_traceSegment_099_1096_0008, g32p_row03_traceSegment_099_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1080 16 17, g32p_row03_traceSegment_099_1080_0016, g32p_row03_traceSegment_099_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1113 8 9, g32p_row03_traceSegment_099_1113_0008, g32p_row03_traceSegment_099_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1130 8 9, g32p_row03_traceSegment_099_1130_0008, g32p_row03_traceSegment_099_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1113 17 17, g32p_row03_traceSegment_099_1113_0017, g32p_row03_traceSegment_099_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1080 33 34, g32p_row03_traceSegment_099_1080_0033, g32p_row03_traceSegment_099_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1147 8 9, g32p_row03_traceSegment_099_1147_0008, g32p_row03_traceSegment_099_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1164 8 9, g32p_row03_traceSegment_099_1164_0008, g32p_row03_traceSegment_099_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1147 17 17, g32p_row03_traceSegment_099_1147_0017, g32p_row03_traceSegment_099_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1181 8 9, g32p_row03_traceSegment_099_1181_0008, g32p_row03_traceSegment_099_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1198 8 9, g32p_row03_traceSegment_099_1198_0008, g32p_row03_traceSegment_099_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1181 17 17, g32p_row03_traceSegment_099_1181_0017, g32p_row03_traceSegment_099_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1147 34 34, g32p_row03_traceSegment_099_1147_0034, g32p_row03_traceSegment_099_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1080 67 68, g32p_row03_traceSegment_099_1080_0067, g32p_row03_traceSegment_099_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1231 8 9, g32p_row03_traceSegment_099_1231_0008, g32p_row03_traceSegment_099_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1215 16 17, g32p_row03_traceSegment_099_1215_0016, g32p_row03_traceSegment_099_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1248 8 9, g32p_row03_traceSegment_099_1248_0008, g32p_row03_traceSegment_099_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1265 8 9, g32p_row03_traceSegment_099_1265_0008, g32p_row03_traceSegment_099_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1248 17 17, g32p_row03_traceSegment_099_1248_0017, g32p_row03_traceSegment_099_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1215 33 34, g32p_row03_traceSegment_099_1215_0033, g32p_row03_traceSegment_099_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1282 8 9, g32p_row03_traceSegment_099_1282_0008, g32p_row03_traceSegment_099_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1299 8 9, g32p_row03_traceSegment_099_1299_0008, g32p_row03_traceSegment_099_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1282 17 17, g32p_row03_traceSegment_099_1282_0017, g32p_row03_traceSegment_099_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1316 8 9, g32p_row03_traceSegment_099_1316_0008, g32p_row03_traceSegment_099_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1333 8 9, g32p_row03_traceSegment_099_1333_0008, g32p_row03_traceSegment_099_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1316 17 17, g32p_row03_traceSegment_099_1316_0017, g32p_row03_traceSegment_099_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1282 34 34, g32p_row03_traceSegment_099_1282_0034, g32p_row03_traceSegment_099_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1215 67 68, g32p_row03_traceSegment_099_1215_0067, g32p_row03_traceSegment_099_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1080 135 135, g32p_row03_traceSegment_099_1080_0135, g32p_row03_traceSegment_099_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1366 8 9, g32p_row03_traceSegment_099_1366_0008, g32p_row03_traceSegment_099_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1350 16 17, g32p_row03_traceSegment_099_1350_0016, g32p_row03_traceSegment_099_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1383 8 9, g32p_row03_traceSegment_099_1383_0008, g32p_row03_traceSegment_099_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1400 8 9, g32p_row03_traceSegment_099_1400_0008, g32p_row03_traceSegment_099_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1383 17 17, g32p_row03_traceSegment_099_1383_0017, g32p_row03_traceSegment_099_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1350 33 34, g32p_row03_traceSegment_099_1350_0033, g32p_row03_traceSegment_099_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1417 8 9, g32p_row03_traceSegment_099_1417_0008, g32p_row03_traceSegment_099_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1434 8 9, g32p_row03_traceSegment_099_1434_0008, g32p_row03_traceSegment_099_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1417 17 17, g32p_row03_traceSegment_099_1417_0017, g32p_row03_traceSegment_099_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1451 8 9, g32p_row03_traceSegment_099_1451_0008, g32p_row03_traceSegment_099_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1468 8 9, g32p_row03_traceSegment_099_1468_0008, g32p_row03_traceSegment_099_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1451 17 17, g32p_row03_traceSegment_099_1451_0017, g32p_row03_traceSegment_099_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1417 34 34, g32p_row03_traceSegment_099_1417_0034, g32p_row03_traceSegment_099_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1350 67 68, g32p_row03_traceSegment_099_1350_0067, g32p_row03_traceSegment_099_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1501 8 9, g32p_row03_traceSegment_099_1501_0008, g32p_row03_traceSegment_099_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1485 16 17, g32p_row03_traceSegment_099_1485_0016, g32p_row03_traceSegment_099_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1518 8 9, g32p_row03_traceSegment_099_1518_0008, g32p_row03_traceSegment_099_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1535 8 9, g32p_row03_traceSegment_099_1535_0008, g32p_row03_traceSegment_099_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1518 17 17, g32p_row03_traceSegment_099_1518_0017, g32p_row03_traceSegment_099_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1485 33 34, g32p_row03_traceSegment_099_1485_0033, g32p_row03_traceSegment_099_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1552 8 9, g32p_row03_traceSegment_099_1552_0008, g32p_row03_traceSegment_099_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1569 8 9, g32p_row03_traceSegment_099_1569_0008, g32p_row03_traceSegment_099_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1552 17 17, g32p_row03_traceSegment_099_1552_0017, g32p_row03_traceSegment_099_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1586 8 9, g32p_row03_traceSegment_099_1586_0008, g32p_row03_traceSegment_099_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1603 8 9, g32p_row03_traceSegment_099_1603_0008, g32p_row03_traceSegment_099_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1586 17 17, g32p_row03_traceSegment_099_1586_0017, g32p_row03_traceSegment_099_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1552 34 34, g32p_row03_traceSegment_099_1552_0034, g32p_row03_traceSegment_099_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1485 67 68, g32p_row03_traceSegment_099_1485_0067, g32p_row03_traceSegment_099_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1350 135 135, g32p_row03_traceSegment_099_1350_0135, g32p_row03_traceSegment_099_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_099 1080 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1080 270 270, g32p_row03_traceSegment_099_1080_0270, g32p_row03_traceSegment_099_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1636 8 9, g32p_row03_traceSegment_099_1636_0008, g32p_row03_traceSegment_099_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1620 16 17, g32p_row03_traceSegment_099_1620_0016, g32p_row03_traceSegment_099_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1653 8 9, g32p_row03_traceSegment_099_1653_0008, g32p_row03_traceSegment_099_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1670 8 9, g32p_row03_traceSegment_099_1670_0008, g32p_row03_traceSegment_099_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1653 17 17, g32p_row03_traceSegment_099_1653_0017, g32p_row03_traceSegment_099_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1620 33 34, g32p_row03_traceSegment_099_1620_0033, g32p_row03_traceSegment_099_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1687 8 9, g32p_row03_traceSegment_099_1687_0008, g32p_row03_traceSegment_099_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1704 8 9, g32p_row03_traceSegment_099_1704_0008, g32p_row03_traceSegment_099_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1687 17 17, g32p_row03_traceSegment_099_1687_0017, g32p_row03_traceSegment_099_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1721 8 9, g32p_row03_traceSegment_099_1721_0008, g32p_row03_traceSegment_099_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1738 8 9, g32p_row03_traceSegment_099_1738_0008, g32p_row03_traceSegment_099_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1721 17 17, g32p_row03_traceSegment_099_1721_0017, g32p_row03_traceSegment_099_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1687 34 34, g32p_row03_traceSegment_099_1687_0034, g32p_row03_traceSegment_099_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1620 67 68, g32p_row03_traceSegment_099_1620_0067, g32p_row03_traceSegment_099_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1771 8 9, g32p_row03_traceSegment_099_1771_0008, g32p_row03_traceSegment_099_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1755 16 17, g32p_row03_traceSegment_099_1755_0016, g32p_row03_traceSegment_099_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1788 8 9, g32p_row03_traceSegment_099_1788_0008, g32p_row03_traceSegment_099_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1805 8 9, g32p_row03_traceSegment_099_1805_0008, g32p_row03_traceSegment_099_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1788 17 17, g32p_row03_traceSegment_099_1788_0017, g32p_row03_traceSegment_099_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1755 33 34, g32p_row03_traceSegment_099_1755_0033, g32p_row03_traceSegment_099_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1822 8 9, g32p_row03_traceSegment_099_1822_0008, g32p_row03_traceSegment_099_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1839 8 9, g32p_row03_traceSegment_099_1839_0008, g32p_row03_traceSegment_099_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1822 17 17, g32p_row03_traceSegment_099_1822_0017, g32p_row03_traceSegment_099_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1856 8 9, g32p_row03_traceSegment_099_1856_0008, g32p_row03_traceSegment_099_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1873 8 9, g32p_row03_traceSegment_099_1873_0008, g32p_row03_traceSegment_099_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1856 17 17, g32p_row03_traceSegment_099_1856_0017, g32p_row03_traceSegment_099_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1822 34 34, g32p_row03_traceSegment_099_1822_0034, g32p_row03_traceSegment_099_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1755 67 68, g32p_row03_traceSegment_099_1755_0067, g32p_row03_traceSegment_099_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1620 135 135, g32p_row03_traceSegment_099_1620_0135, g32p_row03_traceSegment_099_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1906 8 9, g32p_row03_traceSegment_099_1906_0008, g32p_row03_traceSegment_099_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1890 16 17, g32p_row03_traceSegment_099_1890_0016, g32p_row03_traceSegment_099_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1923 8 9, g32p_row03_traceSegment_099_1923_0008, g32p_row03_traceSegment_099_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1940 8 9, g32p_row03_traceSegment_099_1940_0008, g32p_row03_traceSegment_099_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1923 17 17, g32p_row03_traceSegment_099_1923_0017, g32p_row03_traceSegment_099_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1890 33 34, g32p_row03_traceSegment_099_1890_0033, g32p_row03_traceSegment_099_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1957 8 9, g32p_row03_traceSegment_099_1957_0008, g32p_row03_traceSegment_099_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1974 8 9, g32p_row03_traceSegment_099_1974_0008, g32p_row03_traceSegment_099_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1957 17 17, g32p_row03_traceSegment_099_1957_0017, g32p_row03_traceSegment_099_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1991 8 9, g32p_row03_traceSegment_099_1991_0008, g32p_row03_traceSegment_099_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2008 8 9, g32p_row03_traceSegment_099_2008_0008, g32p_row03_traceSegment_099_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1991 17 17, g32p_row03_traceSegment_099_1991_0017, g32p_row03_traceSegment_099_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1957 34 34, g32p_row03_traceSegment_099_1957_0034, g32p_row03_traceSegment_099_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1890 67 68, g32p_row03_traceSegment_099_1890_0067, g32p_row03_traceSegment_099_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2041 8 9, g32p_row03_traceSegment_099_2041_0008, g32p_row03_traceSegment_099_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2025 16 17, g32p_row03_traceSegment_099_2025_0016, g32p_row03_traceSegment_099_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2058 8 9, g32p_row03_traceSegment_099_2058_0008, g32p_row03_traceSegment_099_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2075 8 9, g32p_row03_traceSegment_099_2075_0008, g32p_row03_traceSegment_099_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2058 17 17, g32p_row03_traceSegment_099_2058_0017, g32p_row03_traceSegment_099_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2025 33 34, g32p_row03_traceSegment_099_2025_0033, g32p_row03_traceSegment_099_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2092 8 9, g32p_row03_traceSegment_099_2092_0008, g32p_row03_traceSegment_099_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2109 8 9, g32p_row03_traceSegment_099_2109_0008, g32p_row03_traceSegment_099_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2092 17 17, g32p_row03_traceSegment_099_2092_0017, g32p_row03_traceSegment_099_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2126 8 9, g32p_row03_traceSegment_099_2126_0008, g32p_row03_traceSegment_099_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2143 8 9, g32p_row03_traceSegment_099_2143_0008, g32p_row03_traceSegment_099_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2126 17 17, g32p_row03_traceSegment_099_2126_0017, g32p_row03_traceSegment_099_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2092 34 34, g32p_row03_traceSegment_099_2092_0034, g32p_row03_traceSegment_099_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2025 67 68, g32p_row03_traceSegment_099_2025_0067, g32p_row03_traceSegment_099_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 1890 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1890 135 135, g32p_row03_traceSegment_099_1890_0135, g32p_row03_traceSegment_099_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_099 1620 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1620 270 270, g32p_row03_traceSegment_099_1620_0270, g32p_row03_traceSegment_099_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_099_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_099 1080 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 1080 540 540, g32p_row03_traceSegment_099_1080_0540, g32p_row03_traceSegment_099_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_099 0 2160 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 0 1080 1080, g32p_row03_traceSegment_099_0000_1080, g32p_row03_traceSegment_099_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2176 8 9, g32p_row03_traceSegment_099_2176_0008, g32p_row03_traceSegment_099_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2160 16 17, g32p_row03_traceSegment_099_2160_0016, g32p_row03_traceSegment_099_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2193 8 9, g32p_row03_traceSegment_099_2193_0008, g32p_row03_traceSegment_099_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2210 8 9, g32p_row03_traceSegment_099_2210_0008, g32p_row03_traceSegment_099_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2193 17 17, g32p_row03_traceSegment_099_2193_0017, g32p_row03_traceSegment_099_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2160 33 34, g32p_row03_traceSegment_099_2160_0033, g32p_row03_traceSegment_099_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2227 8 9, g32p_row03_traceSegment_099_2227_0008, g32p_row03_traceSegment_099_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2244 8 9, g32p_row03_traceSegment_099_2244_0008, g32p_row03_traceSegment_099_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2227 17 17, g32p_row03_traceSegment_099_2227_0017, g32p_row03_traceSegment_099_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2261 8 9, g32p_row03_traceSegment_099_2261_0008, g32p_row03_traceSegment_099_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2278 8 9, g32p_row03_traceSegment_099_2278_0008, g32p_row03_traceSegment_099_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2261 17 17, g32p_row03_traceSegment_099_2261_0017, g32p_row03_traceSegment_099_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2227 34 34, g32p_row03_traceSegment_099_2227_0034, g32p_row03_traceSegment_099_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2160 67 68, g32p_row03_traceSegment_099_2160_0067, g32p_row03_traceSegment_099_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2311 8 9, g32p_row03_traceSegment_099_2311_0008, g32p_row03_traceSegment_099_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2295 16 17, g32p_row03_traceSegment_099_2295_0016, g32p_row03_traceSegment_099_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2328 8 9, g32p_row03_traceSegment_099_2328_0008, g32p_row03_traceSegment_099_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2345 8 9, g32p_row03_traceSegment_099_2345_0008, g32p_row03_traceSegment_099_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2328 17 17, g32p_row03_traceSegment_099_2328_0017, g32p_row03_traceSegment_099_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2295 33 34, g32p_row03_traceSegment_099_2295_0033, g32p_row03_traceSegment_099_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2362 8 9, g32p_row03_traceSegment_099_2362_0008, g32p_row03_traceSegment_099_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2379 8 9, g32p_row03_traceSegment_099_2379_0008, g32p_row03_traceSegment_099_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2362 17 17, g32p_row03_traceSegment_099_2362_0017, g32p_row03_traceSegment_099_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2396 8 9, g32p_row03_traceSegment_099_2396_0008, g32p_row03_traceSegment_099_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2413 8 9, g32p_row03_traceSegment_099_2413_0008, g32p_row03_traceSegment_099_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2396 17 17, g32p_row03_traceSegment_099_2396_0017, g32p_row03_traceSegment_099_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2362 34 34, g32p_row03_traceSegment_099_2362_0034, g32p_row03_traceSegment_099_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2295 67 68, g32p_row03_traceSegment_099_2295_0067, g32p_row03_traceSegment_099_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 2160 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2160 135 135, g32p_row03_traceSegment_099_2160_0135, g32p_row03_traceSegment_099_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2446 8 9, g32p_row03_traceSegment_099_2446_0008, g32p_row03_traceSegment_099_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2430 16 17, g32p_row03_traceSegment_099_2430_0016, g32p_row03_traceSegment_099_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2463 8 9, g32p_row03_traceSegment_099_2463_0008, g32p_row03_traceSegment_099_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2480 8 9, g32p_row03_traceSegment_099_2480_0008, g32p_row03_traceSegment_099_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2463 17 17, g32p_row03_traceSegment_099_2463_0017, g32p_row03_traceSegment_099_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2430 33 34, g32p_row03_traceSegment_099_2430_0033, g32p_row03_traceSegment_099_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2497 8 9, g32p_row03_traceSegment_099_2497_0008, g32p_row03_traceSegment_099_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2514 8 9, g32p_row03_traceSegment_099_2514_0008, g32p_row03_traceSegment_099_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2497 17 17, g32p_row03_traceSegment_099_2497_0017, g32p_row03_traceSegment_099_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2531 8 9, g32p_row03_traceSegment_099_2531_0008, g32p_row03_traceSegment_099_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2548 8 9, g32p_row03_traceSegment_099_2548_0008, g32p_row03_traceSegment_099_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2531 17 17, g32p_row03_traceSegment_099_2531_0017, g32p_row03_traceSegment_099_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2497 34 34, g32p_row03_traceSegment_099_2497_0034, g32p_row03_traceSegment_099_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2430 67 68, g32p_row03_traceSegment_099_2430_0067, g32p_row03_traceSegment_099_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2581 8 9, g32p_row03_traceSegment_099_2581_0008, g32p_row03_traceSegment_099_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2565 16 17, g32p_row03_traceSegment_099_2565_0016, g32p_row03_traceSegment_099_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2598 8 9, g32p_row03_traceSegment_099_2598_0008, g32p_row03_traceSegment_099_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2615 8 9, g32p_row03_traceSegment_099_2615_0008, g32p_row03_traceSegment_099_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2598 17 17, g32p_row03_traceSegment_099_2598_0017, g32p_row03_traceSegment_099_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2565 33 34, g32p_row03_traceSegment_099_2565_0033, g32p_row03_traceSegment_099_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2632 8 9, g32p_row03_traceSegment_099_2632_0008, g32p_row03_traceSegment_099_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2649 8 9, g32p_row03_traceSegment_099_2649_0008, g32p_row03_traceSegment_099_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2632 17 17, g32p_row03_traceSegment_099_2632_0017, g32p_row03_traceSegment_099_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2666 8 9, g32p_row03_traceSegment_099_2666_0008, g32p_row03_traceSegment_099_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2683 8 9, g32p_row03_traceSegment_099_2683_0008, g32p_row03_traceSegment_099_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2666 17 17, g32p_row03_traceSegment_099_2666_0017, g32p_row03_traceSegment_099_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2632 34 34, g32p_row03_traceSegment_099_2632_0034, g32p_row03_traceSegment_099_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2565 67 68, g32p_row03_traceSegment_099_2565_0067, g32p_row03_traceSegment_099_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2430 135 135, g32p_row03_traceSegment_099_2430_0135, g32p_row03_traceSegment_099_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_099 2160 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2160 270 270, g32p_row03_traceSegment_099_2160_0270, g32p_row03_traceSegment_099_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2716 8 9, g32p_row03_traceSegment_099_2716_0008, g32p_row03_traceSegment_099_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2700 16 17, g32p_row03_traceSegment_099_2700_0016, g32p_row03_traceSegment_099_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2733 8 9, g32p_row03_traceSegment_099_2733_0008, g32p_row03_traceSegment_099_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2750 8 9, g32p_row03_traceSegment_099_2750_0008, g32p_row03_traceSegment_099_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2733 17 17, g32p_row03_traceSegment_099_2733_0017, g32p_row03_traceSegment_099_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2700 33 34, g32p_row03_traceSegment_099_2700_0033, g32p_row03_traceSegment_099_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2767 8 9, g32p_row03_traceSegment_099_2767_0008, g32p_row03_traceSegment_099_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2784 8 9, g32p_row03_traceSegment_099_2784_0008, g32p_row03_traceSegment_099_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2767 17 17, g32p_row03_traceSegment_099_2767_0017, g32p_row03_traceSegment_099_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2801 8 9, g32p_row03_traceSegment_099_2801_0008, g32p_row03_traceSegment_099_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2818 8 9, g32p_row03_traceSegment_099_2818_0008, g32p_row03_traceSegment_099_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2801 17 17, g32p_row03_traceSegment_099_2801_0017, g32p_row03_traceSegment_099_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2767 34 34, g32p_row03_traceSegment_099_2767_0034, g32p_row03_traceSegment_099_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2700 67 68, g32p_row03_traceSegment_099_2700_0067, g32p_row03_traceSegment_099_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2851 8 9, g32p_row03_traceSegment_099_2851_0008, g32p_row03_traceSegment_099_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2835 16 17, g32p_row03_traceSegment_099_2835_0016, g32p_row03_traceSegment_099_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2868 8 9, g32p_row03_traceSegment_099_2868_0008, g32p_row03_traceSegment_099_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2885 8 9, g32p_row03_traceSegment_099_2885_0008, g32p_row03_traceSegment_099_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2868 17 17, g32p_row03_traceSegment_099_2868_0017, g32p_row03_traceSegment_099_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2835 33 34, g32p_row03_traceSegment_099_2835_0033, g32p_row03_traceSegment_099_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2902 8 9, g32p_row03_traceSegment_099_2902_0008, g32p_row03_traceSegment_099_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2919 8 9, g32p_row03_traceSegment_099_2919_0008, g32p_row03_traceSegment_099_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2902 17 17, g32p_row03_traceSegment_099_2902_0017, g32p_row03_traceSegment_099_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2936 8 9, g32p_row03_traceSegment_099_2936_0008, g32p_row03_traceSegment_099_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2953 8 9, g32p_row03_traceSegment_099_2953_0008, g32p_row03_traceSegment_099_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2936 17 17, g32p_row03_traceSegment_099_2936_0017, g32p_row03_traceSegment_099_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2902 34 34, g32p_row03_traceSegment_099_2902_0034, g32p_row03_traceSegment_099_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2835 67 68, g32p_row03_traceSegment_099_2835_0067, g32p_row03_traceSegment_099_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2700 135 135, g32p_row03_traceSegment_099_2700_0135, g32p_row03_traceSegment_099_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2986 8 9, g32p_row03_traceSegment_099_2986_0008, g32p_row03_traceSegment_099_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2970 16 17, g32p_row03_traceSegment_099_2970_0016, g32p_row03_traceSegment_099_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3003 8 9, g32p_row03_traceSegment_099_3003_0008, g32p_row03_traceSegment_099_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3020 8 9, g32p_row03_traceSegment_099_3020_0008, g32p_row03_traceSegment_099_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3003 17 17, g32p_row03_traceSegment_099_3003_0017, g32p_row03_traceSegment_099_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2970 33 34, g32p_row03_traceSegment_099_2970_0033, g32p_row03_traceSegment_099_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3037 8 9, g32p_row03_traceSegment_099_3037_0008, g32p_row03_traceSegment_099_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3054 8 9, g32p_row03_traceSegment_099_3054_0008, g32p_row03_traceSegment_099_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3037 17 17, g32p_row03_traceSegment_099_3037_0017, g32p_row03_traceSegment_099_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3071 8 9, g32p_row03_traceSegment_099_3071_0008, g32p_row03_traceSegment_099_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3088 8 9, g32p_row03_traceSegment_099_3088_0008, g32p_row03_traceSegment_099_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3071 17 17, g32p_row03_traceSegment_099_3071_0017, g32p_row03_traceSegment_099_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3037 34 34, g32p_row03_traceSegment_099_3037_0034, g32p_row03_traceSegment_099_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2970 67 68, g32p_row03_traceSegment_099_2970_0067, g32p_row03_traceSegment_099_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3121 8 9, g32p_row03_traceSegment_099_3121_0008, g32p_row03_traceSegment_099_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3105 16 17, g32p_row03_traceSegment_099_3105_0016, g32p_row03_traceSegment_099_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3138 8 9, g32p_row03_traceSegment_099_3138_0008, g32p_row03_traceSegment_099_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3155 8 9, g32p_row03_traceSegment_099_3155_0008, g32p_row03_traceSegment_099_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3138 17 17, g32p_row03_traceSegment_099_3138_0017, g32p_row03_traceSegment_099_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3105 33 34, g32p_row03_traceSegment_099_3105_0033, g32p_row03_traceSegment_099_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3172 8 9, g32p_row03_traceSegment_099_3172_0008, g32p_row03_traceSegment_099_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3189 8 9, g32p_row03_traceSegment_099_3189_0008, g32p_row03_traceSegment_099_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3172 17 17, g32p_row03_traceSegment_099_3172_0017, g32p_row03_traceSegment_099_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3206 8 9, g32p_row03_traceSegment_099_3206_0008, g32p_row03_traceSegment_099_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3223 8 9, g32p_row03_traceSegment_099_3223_0008, g32p_row03_traceSegment_099_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3206 17 17, g32p_row03_traceSegment_099_3206_0017, g32p_row03_traceSegment_099_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3172 34 34, g32p_row03_traceSegment_099_3172_0034, g32p_row03_traceSegment_099_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3105 67 68, g32p_row03_traceSegment_099_3105_0067, g32p_row03_traceSegment_099_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2970 135 135, g32p_row03_traceSegment_099_2970_0135, g32p_row03_traceSegment_099_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_099 2700 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2700 270 270, g32p_row03_traceSegment_099_2700_0270, g32p_row03_traceSegment_099_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_099 2160 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2160 540 540, g32p_row03_traceSegment_099_2160_0540, g32p_row03_traceSegment_099_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3256 8 9, g32p_row03_traceSegment_099_3256_0008, g32p_row03_traceSegment_099_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3240 16 17, g32p_row03_traceSegment_099_3240_0016, g32p_row03_traceSegment_099_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3273 8 9, g32p_row03_traceSegment_099_3273_0008, g32p_row03_traceSegment_099_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3290 8 9, g32p_row03_traceSegment_099_3290_0008, g32p_row03_traceSegment_099_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3273 17 17, g32p_row03_traceSegment_099_3273_0017, g32p_row03_traceSegment_099_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3240 33 34, g32p_row03_traceSegment_099_3240_0033, g32p_row03_traceSegment_099_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3307 8 9, g32p_row03_traceSegment_099_3307_0008, g32p_row03_traceSegment_099_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3324 8 9, g32p_row03_traceSegment_099_3324_0008, g32p_row03_traceSegment_099_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3307 17 17, g32p_row03_traceSegment_099_3307_0017, g32p_row03_traceSegment_099_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3341 8 9, g32p_row03_traceSegment_099_3341_0008, g32p_row03_traceSegment_099_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3358 8 9, g32p_row03_traceSegment_099_3358_0008, g32p_row03_traceSegment_099_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3341 17 17, g32p_row03_traceSegment_099_3341_0017, g32p_row03_traceSegment_099_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3307 34 34, g32p_row03_traceSegment_099_3307_0034, g32p_row03_traceSegment_099_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3240 67 68, g32p_row03_traceSegment_099_3240_0067, g32p_row03_traceSegment_099_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3391 8 9, g32p_row03_traceSegment_099_3391_0008, g32p_row03_traceSegment_099_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3375 16 17, g32p_row03_traceSegment_099_3375_0016, g32p_row03_traceSegment_099_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3408 8 9, g32p_row03_traceSegment_099_3408_0008, g32p_row03_traceSegment_099_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3425 8 9, g32p_row03_traceSegment_099_3425_0008, g32p_row03_traceSegment_099_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3408 17 17, g32p_row03_traceSegment_099_3408_0017, g32p_row03_traceSegment_099_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3375 33 34, g32p_row03_traceSegment_099_3375_0033, g32p_row03_traceSegment_099_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3442 8 9, g32p_row03_traceSegment_099_3442_0008, g32p_row03_traceSegment_099_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3459 8 9, g32p_row03_traceSegment_099_3459_0008, g32p_row03_traceSegment_099_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3442 17 17, g32p_row03_traceSegment_099_3442_0017, g32p_row03_traceSegment_099_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3476 8 9, g32p_row03_traceSegment_099_3476_0008, g32p_row03_traceSegment_099_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3493 8 9, g32p_row03_traceSegment_099_3493_0008, g32p_row03_traceSegment_099_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3476 17 17, g32p_row03_traceSegment_099_3476_0017, g32p_row03_traceSegment_099_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3442 34 34, g32p_row03_traceSegment_099_3442_0034, g32p_row03_traceSegment_099_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3375 67 68, g32p_row03_traceSegment_099_3375_0067, g32p_row03_traceSegment_099_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3240 135 135, g32p_row03_traceSegment_099_3240_0135, g32p_row03_traceSegment_099_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3526 8 9, g32p_row03_traceSegment_099_3526_0008, g32p_row03_traceSegment_099_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3510 16 17, g32p_row03_traceSegment_099_3510_0016, g32p_row03_traceSegment_099_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3543 8 9, g32p_row03_traceSegment_099_3543_0008, g32p_row03_traceSegment_099_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3560 8 9, g32p_row03_traceSegment_099_3560_0008, g32p_row03_traceSegment_099_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3543 17 17, g32p_row03_traceSegment_099_3543_0017, g32p_row03_traceSegment_099_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3510 33 34, g32p_row03_traceSegment_099_3510_0033, g32p_row03_traceSegment_099_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3577 8 9, g32p_row03_traceSegment_099_3577_0008, g32p_row03_traceSegment_099_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3594 8 9, g32p_row03_traceSegment_099_3594_0008, g32p_row03_traceSegment_099_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3577 17 17, g32p_row03_traceSegment_099_3577_0017, g32p_row03_traceSegment_099_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3611 8 9, g32p_row03_traceSegment_099_3611_0008, g32p_row03_traceSegment_099_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3628 8 9, g32p_row03_traceSegment_099_3628_0008, g32p_row03_traceSegment_099_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3611 17 17, g32p_row03_traceSegment_099_3611_0017, g32p_row03_traceSegment_099_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3577 34 34, g32p_row03_traceSegment_099_3577_0034, g32p_row03_traceSegment_099_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3510 67 68, g32p_row03_traceSegment_099_3510_0067, g32p_row03_traceSegment_099_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3661 8 9, g32p_row03_traceSegment_099_3661_0008, g32p_row03_traceSegment_099_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3645 16 17, g32p_row03_traceSegment_099_3645_0016, g32p_row03_traceSegment_099_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3678 8 9, g32p_row03_traceSegment_099_3678_0008, g32p_row03_traceSegment_099_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3695 8 9, g32p_row03_traceSegment_099_3695_0008, g32p_row03_traceSegment_099_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3678 17 17, g32p_row03_traceSegment_099_3678_0017, g32p_row03_traceSegment_099_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3645 33 34, g32p_row03_traceSegment_099_3645_0033, g32p_row03_traceSegment_099_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3712 8 9, g32p_row03_traceSegment_099_3712_0008, g32p_row03_traceSegment_099_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3729 8 9, g32p_row03_traceSegment_099_3729_0008, g32p_row03_traceSegment_099_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3712 17 17, g32p_row03_traceSegment_099_3712_0017, g32p_row03_traceSegment_099_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3746 8 9, g32p_row03_traceSegment_099_3746_0008, g32p_row03_traceSegment_099_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3763 8 9, g32p_row03_traceSegment_099_3763_0008, g32p_row03_traceSegment_099_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3746 17 17, g32p_row03_traceSegment_099_3746_0017, g32p_row03_traceSegment_099_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3712 34 34, g32p_row03_traceSegment_099_3712_0034, g32p_row03_traceSegment_099_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3645 67 68, g32p_row03_traceSegment_099_3645_0067, g32p_row03_traceSegment_099_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 3510 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3510 135 135, g32p_row03_traceSegment_099_3510_0135, g32p_row03_traceSegment_099_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_099 3240 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3240 270 270, g32p_row03_traceSegment_099_3240_0270, g32p_row03_traceSegment_099_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3796 8 9, g32p_row03_traceSegment_099_3796_0008, g32p_row03_traceSegment_099_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3780 16 17, g32p_row03_traceSegment_099_3780_0016, g32p_row03_traceSegment_099_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3813 8 9, g32p_row03_traceSegment_099_3813_0008, g32p_row03_traceSegment_099_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3830 8 9, g32p_row03_traceSegment_099_3830_0008, g32p_row03_traceSegment_099_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3813 17 17, g32p_row03_traceSegment_099_3813_0017, g32p_row03_traceSegment_099_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3780 33 34, g32p_row03_traceSegment_099_3780_0033, g32p_row03_traceSegment_099_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3847 8 9, g32p_row03_traceSegment_099_3847_0008, g32p_row03_traceSegment_099_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3864 8 9, g32p_row03_traceSegment_099_3864_0008, g32p_row03_traceSegment_099_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3847 17 17, g32p_row03_traceSegment_099_3847_0017, g32p_row03_traceSegment_099_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3881 8 9, g32p_row03_traceSegment_099_3881_0008, g32p_row03_traceSegment_099_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3898 8 9, g32p_row03_traceSegment_099_3898_0008, g32p_row03_traceSegment_099_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3881 17 17, g32p_row03_traceSegment_099_3881_0017, g32p_row03_traceSegment_099_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3847 34 34, g32p_row03_traceSegment_099_3847_0034, g32p_row03_traceSegment_099_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3780 67 68, g32p_row03_traceSegment_099_3780_0067, g32p_row03_traceSegment_099_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3931 8 9, g32p_row03_traceSegment_099_3931_0008, g32p_row03_traceSegment_099_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3915 16 17, g32p_row03_traceSegment_099_3915_0016, g32p_row03_traceSegment_099_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3948 8 9, g32p_row03_traceSegment_099_3948_0008, g32p_row03_traceSegment_099_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3965 8 9, g32p_row03_traceSegment_099_3965_0008, g32p_row03_traceSegment_099_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3948 17 17, g32p_row03_traceSegment_099_3948_0017, g32p_row03_traceSegment_099_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3915 33 34, g32p_row03_traceSegment_099_3915_0033, g32p_row03_traceSegment_099_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3982 8 9, g32p_row03_traceSegment_099_3982_0008, g32p_row03_traceSegment_099_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3999 8 9, g32p_row03_traceSegment_099_3999_0008, g32p_row03_traceSegment_099_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3982 17 17, g32p_row03_traceSegment_099_3982_0017, g32p_row03_traceSegment_099_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4016 8 9, g32p_row03_traceSegment_099_4016_0008, g32p_row03_traceSegment_099_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4033 8 9, g32p_row03_traceSegment_099_4033_0008, g32p_row03_traceSegment_099_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4016 17 17, g32p_row03_traceSegment_099_4016_0017, g32p_row03_traceSegment_099_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3982 34 34, g32p_row03_traceSegment_099_3982_0034, g32p_row03_traceSegment_099_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3915 67 68, g32p_row03_traceSegment_099_3915_0067, g32p_row03_traceSegment_099_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3780 135 135, g32p_row03_traceSegment_099_3780_0135, g32p_row03_traceSegment_099_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4066 8 9, g32p_row03_traceSegment_099_4066_0008, g32p_row03_traceSegment_099_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4050 16 17, g32p_row03_traceSegment_099_4050_0016, g32p_row03_traceSegment_099_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4083 8 9, g32p_row03_traceSegment_099_4083_0008, g32p_row03_traceSegment_099_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4100 8 9, g32p_row03_traceSegment_099_4100_0008, g32p_row03_traceSegment_099_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4083 17 17, g32p_row03_traceSegment_099_4083_0017, g32p_row03_traceSegment_099_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4050 33 34, g32p_row03_traceSegment_099_4050_0033, g32p_row03_traceSegment_099_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4117 8 9, g32p_row03_traceSegment_099_4117_0008, g32p_row03_traceSegment_099_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4134 8 9, g32p_row03_traceSegment_099_4134_0008, g32p_row03_traceSegment_099_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4117 17 17, g32p_row03_traceSegment_099_4117_0017, g32p_row03_traceSegment_099_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4151 8 9, g32p_row03_traceSegment_099_4151_0008, g32p_row03_traceSegment_099_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4168 8 9, g32p_row03_traceSegment_099_4168_0008, g32p_row03_traceSegment_099_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4151 17 17, g32p_row03_traceSegment_099_4151_0017, g32p_row03_traceSegment_099_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4117 34 34, g32p_row03_traceSegment_099_4117_0034, g32p_row03_traceSegment_099_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4050 67 68, g32p_row03_traceSegment_099_4050_0067, g32p_row03_traceSegment_099_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_099 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4201 8 9, g32p_row03_traceSegment_099_4201_0008, g32p_row03_traceSegment_099_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_099 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4185 16 17, g32p_row03_traceSegment_099_4185_0016, g32p_row03_traceSegment_099_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4218 8 9, g32p_row03_traceSegment_099_4218_0008, g32p_row03_traceSegment_099_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4235 8 9, g32p_row03_traceSegment_099_4235_0008, g32p_row03_traceSegment_099_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4218 17 17, g32p_row03_traceSegment_099_4218_0017, g32p_row03_traceSegment_099_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_099 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4185 33 34, g32p_row03_traceSegment_099_4185_0033, g32p_row03_traceSegment_099_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4252 8 9, g32p_row03_traceSegment_099_4252_0008, g32p_row03_traceSegment_099_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4269 8 9, g32p_row03_traceSegment_099_4269_0008, g32p_row03_traceSegment_099_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4252 17 17, g32p_row03_traceSegment_099_4252_0017, g32p_row03_traceSegment_099_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4286 8 9, g32p_row03_traceSegment_099_4286_0008, g32p_row03_traceSegment_099_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_099 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_099 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_099_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_099 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4303 8 9, g32p_row03_traceSegment_099_4303_0008, g32p_row03_traceSegment_099_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_099 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4286 17 17, g32p_row03_traceSegment_099_4286_0017, g32p_row03_traceSegment_099_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_099 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4252 34 34, g32p_row03_traceSegment_099_4252_0034, g32p_row03_traceSegment_099_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_099 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4185 67 68, g32p_row03_traceSegment_099_4185_0067, g32p_row03_traceSegment_099_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_099_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_099 4050 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 4050 135 135, g32p_row03_traceSegment_099_4050_0135, g32p_row03_traceSegment_099_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_099 3780 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3780 270 270, g32p_row03_traceSegment_099_3780_0270, g32p_row03_traceSegment_099_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_099_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_099 3240 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 3240 540 540, g32p_row03_traceSegment_099_3240_0540, g32p_row03_traceSegment_099_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_099_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_099 2160 2160 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 2160 1080 1080, g32p_row03_traceSegment_099_2160_1080, g32p_row03_traceSegment_099_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_099_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_099 0 4320 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_099 0 2160 2160, g32p_row03_traceSegment_099_0000_2160, g32p_row03_traceSegment_099_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_099_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_101_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 16 8 9, g32p_row03_traceSegment_101_0016_0008, g32p_row03_traceSegment_101_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 0 16 17, g32p_row03_traceSegment_101_0000_0016, g32p_row03_traceSegment_101_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 33 8 9, g32p_row03_traceSegment_101_0033_0008, g32p_row03_traceSegment_101_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 50 8 9, g32p_row03_traceSegment_101_0050_0008, g32p_row03_traceSegment_101_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 33 17 17, g32p_row03_traceSegment_101_0033_0017, g32p_row03_traceSegment_101_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 0 33 34, g32p_row03_traceSegment_101_0000_0033, g32p_row03_traceSegment_101_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 67 8 9, g32p_row03_traceSegment_101_0067_0008, g32p_row03_traceSegment_101_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 84 8 9, g32p_row03_traceSegment_101_0084_0008, g32p_row03_traceSegment_101_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 67 17 17, g32p_row03_traceSegment_101_0067_0017, g32p_row03_traceSegment_101_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 101 8 9, g32p_row03_traceSegment_101_0101_0008, g32p_row03_traceSegment_101_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 118 8 9, g32p_row03_traceSegment_101_0118_0008, g32p_row03_traceSegment_101_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 101 17 17, g32p_row03_traceSegment_101_0101_0017, g32p_row03_traceSegment_101_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 67 34 34, g32p_row03_traceSegment_101_0067_0034, g32p_row03_traceSegment_101_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 0 67 68, g32p_row03_traceSegment_101_0000_0067, g32p_row03_traceSegment_101_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 151 8 9, g32p_row03_traceSegment_101_0151_0008, g32p_row03_traceSegment_101_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 135 16 17, g32p_row03_traceSegment_101_0135_0016, g32p_row03_traceSegment_101_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 168 8 9, g32p_row03_traceSegment_101_0168_0008, g32p_row03_traceSegment_101_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 185 8 9, g32p_row03_traceSegment_101_0185_0008, g32p_row03_traceSegment_101_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 168 17 17, g32p_row03_traceSegment_101_0168_0017, g32p_row03_traceSegment_101_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 135 33 34, g32p_row03_traceSegment_101_0135_0033, g32p_row03_traceSegment_101_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 202 8 9, g32p_row03_traceSegment_101_0202_0008, g32p_row03_traceSegment_101_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 219 8 9, g32p_row03_traceSegment_101_0219_0008, g32p_row03_traceSegment_101_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 202 17 17, g32p_row03_traceSegment_101_0202_0017, g32p_row03_traceSegment_101_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 236 8 9, g32p_row03_traceSegment_101_0236_0008, g32p_row03_traceSegment_101_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 253 8 9, g32p_row03_traceSegment_101_0253_0008, g32p_row03_traceSegment_101_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 236 17 17, g32p_row03_traceSegment_101_0236_0017, g32p_row03_traceSegment_101_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 202 34 34, g32p_row03_traceSegment_101_0202_0034, g32p_row03_traceSegment_101_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 135 67 68, g32p_row03_traceSegment_101_0135_0067, g32p_row03_traceSegment_101_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 0 135 135, g32p_row03_traceSegment_101_0000_0135, g32p_row03_traceSegment_101_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 286 8 9, g32p_row03_traceSegment_101_0286_0008, g32p_row03_traceSegment_101_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 270 16 17, g32p_row03_traceSegment_101_0270_0016, g32p_row03_traceSegment_101_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 303 8 9, g32p_row03_traceSegment_101_0303_0008, g32p_row03_traceSegment_101_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 320 8 9, g32p_row03_traceSegment_101_0320_0008, g32p_row03_traceSegment_101_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 303 17 17, g32p_row03_traceSegment_101_0303_0017, g32p_row03_traceSegment_101_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 270 33 34, g32p_row03_traceSegment_101_0270_0033, g32p_row03_traceSegment_101_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 337 8 9, g32p_row03_traceSegment_101_0337_0008, g32p_row03_traceSegment_101_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 354 8 9, g32p_row03_traceSegment_101_0354_0008, g32p_row03_traceSegment_101_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 337 17 17, g32p_row03_traceSegment_101_0337_0017, g32p_row03_traceSegment_101_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 371 8 9, g32p_row03_traceSegment_101_0371_0008, g32p_row03_traceSegment_101_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 396 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 388 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 388 8 9, g32p_row03_traceSegment_101_0388_0008, g32p_row03_traceSegment_101_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 371 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 371 17 17, g32p_row03_traceSegment_101_0371_0017, g32p_row03_traceSegment_101_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 337 68 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 337 34 34, g32p_row03_traceSegment_101_0337_0034, g32p_row03_traceSegment_101_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 270 135 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 270 67 68, g32p_row03_traceSegment_101_0270_0067, g32p_row03_traceSegment_101_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 421 8 9, g32p_row03_traceSegment_101_0421_0008, g32p_row03_traceSegment_101_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 405 16 17, g32p_row03_traceSegment_101_0405_0016, g32p_row03_traceSegment_101_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 438 8 9, g32p_row03_traceSegment_101_0438_0008, g32p_row03_traceSegment_101_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 455 8 9, g32p_row03_traceSegment_101_0455_0008, g32p_row03_traceSegment_101_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 438 17 17, g32p_row03_traceSegment_101_0438_0017, g32p_row03_traceSegment_101_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 405 33 34, g32p_row03_traceSegment_101_0405_0033, g32p_row03_traceSegment_101_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 472 8 9, g32p_row03_traceSegment_101_0472_0008, g32p_row03_traceSegment_101_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 489 8 9, g32p_row03_traceSegment_101_0489_0008, g32p_row03_traceSegment_101_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 472 17 17, g32p_row03_traceSegment_101_0472_0017, g32p_row03_traceSegment_101_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 506 8 9, g32p_row03_traceSegment_101_0506_0008, g32p_row03_traceSegment_101_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 523 8 9, g32p_row03_traceSegment_101_0523_0008, g32p_row03_traceSegment_101_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 506 17 17, g32p_row03_traceSegment_101_0506_0017, g32p_row03_traceSegment_101_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 472 34 34, g32p_row03_traceSegment_101_0472_0034, g32p_row03_traceSegment_101_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 405 67 68, g32p_row03_traceSegment_101_0405_0067, g32p_row03_traceSegment_101_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 270 270 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 270 135 135, g32p_row03_traceSegment_101_0270_0135, g32p_row03_traceSegment_101_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_101 0 540 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 0 270 270, g32p_row03_traceSegment_101_0000_0270, g32p_row03_traceSegment_101_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 556 8 9, g32p_row03_traceSegment_101_0556_0008, g32p_row03_traceSegment_101_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 540 16 17, g32p_row03_traceSegment_101_0540_0016, g32p_row03_traceSegment_101_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 573 8 9, g32p_row03_traceSegment_101_0573_0008, g32p_row03_traceSegment_101_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 590 8 9, g32p_row03_traceSegment_101_0590_0008, g32p_row03_traceSegment_101_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 573 17 17, g32p_row03_traceSegment_101_0573_0017, g32p_row03_traceSegment_101_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 540 33 34, g32p_row03_traceSegment_101_0540_0033, g32p_row03_traceSegment_101_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 607 8 9, g32p_row03_traceSegment_101_0607_0008, g32p_row03_traceSegment_101_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 624 8 9, g32p_row03_traceSegment_101_0624_0008, g32p_row03_traceSegment_101_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 607 17 17, g32p_row03_traceSegment_101_0607_0017, g32p_row03_traceSegment_101_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 641 8 9, g32p_row03_traceSegment_101_0641_0008, g32p_row03_traceSegment_101_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 658 8 9, g32p_row03_traceSegment_101_0658_0008, g32p_row03_traceSegment_101_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 641 17 17, g32p_row03_traceSegment_101_0641_0017, g32p_row03_traceSegment_101_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 607 34 34, g32p_row03_traceSegment_101_0607_0034, g32p_row03_traceSegment_101_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 540 67 68, g32p_row03_traceSegment_101_0540_0067, g32p_row03_traceSegment_101_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 691 8 9, g32p_row03_traceSegment_101_0691_0008, g32p_row03_traceSegment_101_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 675 16 17, g32p_row03_traceSegment_101_0675_0016, g32p_row03_traceSegment_101_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 708 8 9, g32p_row03_traceSegment_101_0708_0008, g32p_row03_traceSegment_101_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 725 8 9, g32p_row03_traceSegment_101_0725_0008, g32p_row03_traceSegment_101_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 708 17 17, g32p_row03_traceSegment_101_0708_0017, g32p_row03_traceSegment_101_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 675 33 34, g32p_row03_traceSegment_101_0675_0033, g32p_row03_traceSegment_101_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 742 8 9, g32p_row03_traceSegment_101_0742_0008, g32p_row03_traceSegment_101_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 759 8 9, g32p_row03_traceSegment_101_0759_0008, g32p_row03_traceSegment_101_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 742 17 17, g32p_row03_traceSegment_101_0742_0017, g32p_row03_traceSegment_101_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 776 8 9, g32p_row03_traceSegment_101_0776_0008, g32p_row03_traceSegment_101_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 793 8 9, g32p_row03_traceSegment_101_0793_0008, g32p_row03_traceSegment_101_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 776 17 17, g32p_row03_traceSegment_101_0776_0017, g32p_row03_traceSegment_101_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 742 34 34, g32p_row03_traceSegment_101_0742_0034, g32p_row03_traceSegment_101_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 675 67 68, g32p_row03_traceSegment_101_0675_0067, g32p_row03_traceSegment_101_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 540 135 135, g32p_row03_traceSegment_101_0540_0135, g32p_row03_traceSegment_101_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 826 8 9, g32p_row03_traceSegment_101_0826_0008, g32p_row03_traceSegment_101_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 810 16 17, g32p_row03_traceSegment_101_0810_0016, g32p_row03_traceSegment_101_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 843 8 9, g32p_row03_traceSegment_101_0843_0008, g32p_row03_traceSegment_101_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 860 8 9, g32p_row03_traceSegment_101_0860_0008, g32p_row03_traceSegment_101_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 843 17 17, g32p_row03_traceSegment_101_0843_0017, g32p_row03_traceSegment_101_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 810 33 34, g32p_row03_traceSegment_101_0810_0033, g32p_row03_traceSegment_101_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 877 8 9, g32p_row03_traceSegment_101_0877_0008, g32p_row03_traceSegment_101_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 894 8 9, g32p_row03_traceSegment_101_0894_0008, g32p_row03_traceSegment_101_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 877 17 17, g32p_row03_traceSegment_101_0877_0017, g32p_row03_traceSegment_101_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 911 8 9, g32p_row03_traceSegment_101_0911_0008, g32p_row03_traceSegment_101_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 928 8 9, g32p_row03_traceSegment_101_0928_0008, g32p_row03_traceSegment_101_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 911 17 17, g32p_row03_traceSegment_101_0911_0017, g32p_row03_traceSegment_101_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 877 34 34, g32p_row03_traceSegment_101_0877_0034, g32p_row03_traceSegment_101_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 810 67 68, g32p_row03_traceSegment_101_0810_0067, g32p_row03_traceSegment_101_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 961 8 9, g32p_row03_traceSegment_101_0961_0008, g32p_row03_traceSegment_101_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 945 16 17, g32p_row03_traceSegment_101_0945_0016, g32p_row03_traceSegment_101_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 978 8 9, g32p_row03_traceSegment_101_0978_0008, g32p_row03_traceSegment_101_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 995 8 9, g32p_row03_traceSegment_101_0995_0008, g32p_row03_traceSegment_101_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 978 17 17, g32p_row03_traceSegment_101_0978_0017, g32p_row03_traceSegment_101_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 945 33 34, g32p_row03_traceSegment_101_0945_0033, g32p_row03_traceSegment_101_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1012 8 9, g32p_row03_traceSegment_101_1012_0008, g32p_row03_traceSegment_101_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1029 8 9, g32p_row03_traceSegment_101_1029_0008, g32p_row03_traceSegment_101_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1012 17 17, g32p_row03_traceSegment_101_1012_0017, g32p_row03_traceSegment_101_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1046 8 9, g32p_row03_traceSegment_101_1046_0008, g32p_row03_traceSegment_101_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1063 8 9, g32p_row03_traceSegment_101_1063_0008, g32p_row03_traceSegment_101_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1046 17 17, g32p_row03_traceSegment_101_1046_0017, g32p_row03_traceSegment_101_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1012 34 34, g32p_row03_traceSegment_101_1012_0034, g32p_row03_traceSegment_101_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 945 67 68, g32p_row03_traceSegment_101_0945_0067, g32p_row03_traceSegment_101_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 810 135 135, g32p_row03_traceSegment_101_0810_0135, g32p_row03_traceSegment_101_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_101 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 540 270 270, g32p_row03_traceSegment_101_0540_0270, g32p_row03_traceSegment_101_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_101 0 1080 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 0 540 540, g32p_row03_traceSegment_101_0000_0540, g32p_row03_traceSegment_101_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1096 8 9, g32p_row03_traceSegment_101_1096_0008, g32p_row03_traceSegment_101_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1080 16 17, g32p_row03_traceSegment_101_1080_0016, g32p_row03_traceSegment_101_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1113 8 9, g32p_row03_traceSegment_101_1113_0008, g32p_row03_traceSegment_101_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1130 8 9, g32p_row03_traceSegment_101_1130_0008, g32p_row03_traceSegment_101_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1113 17 17, g32p_row03_traceSegment_101_1113_0017, g32p_row03_traceSegment_101_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1080 33 34, g32p_row03_traceSegment_101_1080_0033, g32p_row03_traceSegment_101_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1147 8 9, g32p_row03_traceSegment_101_1147_0008, g32p_row03_traceSegment_101_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1164 8 9, g32p_row03_traceSegment_101_1164_0008, g32p_row03_traceSegment_101_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1147 17 17, g32p_row03_traceSegment_101_1147_0017, g32p_row03_traceSegment_101_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1181 8 9, g32p_row03_traceSegment_101_1181_0008, g32p_row03_traceSegment_101_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1198 8 9, g32p_row03_traceSegment_101_1198_0008, g32p_row03_traceSegment_101_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1181 17 17, g32p_row03_traceSegment_101_1181_0017, g32p_row03_traceSegment_101_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1147 34 34, g32p_row03_traceSegment_101_1147_0034, g32p_row03_traceSegment_101_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1080 67 68, g32p_row03_traceSegment_101_1080_0067, g32p_row03_traceSegment_101_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1231 8 9, g32p_row03_traceSegment_101_1231_0008, g32p_row03_traceSegment_101_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1215 16 17, g32p_row03_traceSegment_101_1215_0016, g32p_row03_traceSegment_101_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1248 8 9, g32p_row03_traceSegment_101_1248_0008, g32p_row03_traceSegment_101_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1265 8 9, g32p_row03_traceSegment_101_1265_0008, g32p_row03_traceSegment_101_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1248 17 17, g32p_row03_traceSegment_101_1248_0017, g32p_row03_traceSegment_101_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1215 33 34, g32p_row03_traceSegment_101_1215_0033, g32p_row03_traceSegment_101_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1282 8 9, g32p_row03_traceSegment_101_1282_0008, g32p_row03_traceSegment_101_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1299 8 9, g32p_row03_traceSegment_101_1299_0008, g32p_row03_traceSegment_101_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1282 17 17, g32p_row03_traceSegment_101_1282_0017, g32p_row03_traceSegment_101_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1316 8 9, g32p_row03_traceSegment_101_1316_0008, g32p_row03_traceSegment_101_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1333 8 9, g32p_row03_traceSegment_101_1333_0008, g32p_row03_traceSegment_101_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1316 17 17, g32p_row03_traceSegment_101_1316_0017, g32p_row03_traceSegment_101_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1282 34 34, g32p_row03_traceSegment_101_1282_0034, g32p_row03_traceSegment_101_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1215 67 68, g32p_row03_traceSegment_101_1215_0067, g32p_row03_traceSegment_101_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1080 135 135, g32p_row03_traceSegment_101_1080_0135, g32p_row03_traceSegment_101_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1366 8 9, g32p_row03_traceSegment_101_1366_0008, g32p_row03_traceSegment_101_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1350 16 17, g32p_row03_traceSegment_101_1350_0016, g32p_row03_traceSegment_101_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1383 8 9, g32p_row03_traceSegment_101_1383_0008, g32p_row03_traceSegment_101_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1400 8 9, g32p_row03_traceSegment_101_1400_0008, g32p_row03_traceSegment_101_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1383 17 17, g32p_row03_traceSegment_101_1383_0017, g32p_row03_traceSegment_101_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1350 33 34, g32p_row03_traceSegment_101_1350_0033, g32p_row03_traceSegment_101_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1417 8 9, g32p_row03_traceSegment_101_1417_0008, g32p_row03_traceSegment_101_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1434 8 9, g32p_row03_traceSegment_101_1434_0008, g32p_row03_traceSegment_101_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1417 17 17, g32p_row03_traceSegment_101_1417_0017, g32p_row03_traceSegment_101_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1451 8 9, g32p_row03_traceSegment_101_1451_0008, g32p_row03_traceSegment_101_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1468 8 9, g32p_row03_traceSegment_101_1468_0008, g32p_row03_traceSegment_101_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1451 17 17, g32p_row03_traceSegment_101_1451_0017, g32p_row03_traceSegment_101_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1417 34 34, g32p_row03_traceSegment_101_1417_0034, g32p_row03_traceSegment_101_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1350 67 68, g32p_row03_traceSegment_101_1350_0067, g32p_row03_traceSegment_101_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1501 8 9, g32p_row03_traceSegment_101_1501_0008, g32p_row03_traceSegment_101_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1485 16 17, g32p_row03_traceSegment_101_1485_0016, g32p_row03_traceSegment_101_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1518 8 9, g32p_row03_traceSegment_101_1518_0008, g32p_row03_traceSegment_101_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1535 8 9, g32p_row03_traceSegment_101_1535_0008, g32p_row03_traceSegment_101_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1518 17 17, g32p_row03_traceSegment_101_1518_0017, g32p_row03_traceSegment_101_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1485 33 34, g32p_row03_traceSegment_101_1485_0033, g32p_row03_traceSegment_101_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1552 8 9, g32p_row03_traceSegment_101_1552_0008, g32p_row03_traceSegment_101_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1569 8 9, g32p_row03_traceSegment_101_1569_0008, g32p_row03_traceSegment_101_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1552 17 17, g32p_row03_traceSegment_101_1552_0017, g32p_row03_traceSegment_101_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1586 8 9, g32p_row03_traceSegment_101_1586_0008, g32p_row03_traceSegment_101_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1603 8 9, g32p_row03_traceSegment_101_1603_0008, g32p_row03_traceSegment_101_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1586 17 17, g32p_row03_traceSegment_101_1586_0017, g32p_row03_traceSegment_101_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1552 34 34, g32p_row03_traceSegment_101_1552_0034, g32p_row03_traceSegment_101_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1485 67 68, g32p_row03_traceSegment_101_1485_0067, g32p_row03_traceSegment_101_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1350 135 135, g32p_row03_traceSegment_101_1350_0135, g32p_row03_traceSegment_101_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_101 1080 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1080 270 270, g32p_row03_traceSegment_101_1080_0270, g32p_row03_traceSegment_101_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1636 8 9, g32p_row03_traceSegment_101_1636_0008, g32p_row03_traceSegment_101_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1620 16 17, g32p_row03_traceSegment_101_1620_0016, g32p_row03_traceSegment_101_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1653 8 9, g32p_row03_traceSegment_101_1653_0008, g32p_row03_traceSegment_101_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1670 8 9, g32p_row03_traceSegment_101_1670_0008, g32p_row03_traceSegment_101_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1653 17 17, g32p_row03_traceSegment_101_1653_0017, g32p_row03_traceSegment_101_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1620 33 34, g32p_row03_traceSegment_101_1620_0033, g32p_row03_traceSegment_101_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1687 8 9, g32p_row03_traceSegment_101_1687_0008, g32p_row03_traceSegment_101_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1704 8 9, g32p_row03_traceSegment_101_1704_0008, g32p_row03_traceSegment_101_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1687 17 17, g32p_row03_traceSegment_101_1687_0017, g32p_row03_traceSegment_101_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1721 8 9, g32p_row03_traceSegment_101_1721_0008, g32p_row03_traceSegment_101_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1738 8 9, g32p_row03_traceSegment_101_1738_0008, g32p_row03_traceSegment_101_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1721 17 17, g32p_row03_traceSegment_101_1721_0017, g32p_row03_traceSegment_101_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1687 34 34, g32p_row03_traceSegment_101_1687_0034, g32p_row03_traceSegment_101_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1620 67 68, g32p_row03_traceSegment_101_1620_0067, g32p_row03_traceSegment_101_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1771 8 9, g32p_row03_traceSegment_101_1771_0008, g32p_row03_traceSegment_101_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1755 16 17, g32p_row03_traceSegment_101_1755_0016, g32p_row03_traceSegment_101_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1788 8 9, g32p_row03_traceSegment_101_1788_0008, g32p_row03_traceSegment_101_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1805 8 9, g32p_row03_traceSegment_101_1805_0008, g32p_row03_traceSegment_101_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1788 17 17, g32p_row03_traceSegment_101_1788_0017, g32p_row03_traceSegment_101_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1755 33 34, g32p_row03_traceSegment_101_1755_0033, g32p_row03_traceSegment_101_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1822 8 9, g32p_row03_traceSegment_101_1822_0008, g32p_row03_traceSegment_101_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1839 8 9, g32p_row03_traceSegment_101_1839_0008, g32p_row03_traceSegment_101_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1822 17 17, g32p_row03_traceSegment_101_1822_0017, g32p_row03_traceSegment_101_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1856 8 9, g32p_row03_traceSegment_101_1856_0008, g32p_row03_traceSegment_101_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1873 8 9, g32p_row03_traceSegment_101_1873_0008, g32p_row03_traceSegment_101_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1856 17 17, g32p_row03_traceSegment_101_1856_0017, g32p_row03_traceSegment_101_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1822 34 34, g32p_row03_traceSegment_101_1822_0034, g32p_row03_traceSegment_101_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1755 67 68, g32p_row03_traceSegment_101_1755_0067, g32p_row03_traceSegment_101_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1620 135 135, g32p_row03_traceSegment_101_1620_0135, g32p_row03_traceSegment_101_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1906 8 9, g32p_row03_traceSegment_101_1906_0008, g32p_row03_traceSegment_101_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1890 16 17, g32p_row03_traceSegment_101_1890_0016, g32p_row03_traceSegment_101_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1923 8 9, g32p_row03_traceSegment_101_1923_0008, g32p_row03_traceSegment_101_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1940 8 9, g32p_row03_traceSegment_101_1940_0008, g32p_row03_traceSegment_101_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1923 17 17, g32p_row03_traceSegment_101_1923_0017, g32p_row03_traceSegment_101_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1890 33 34, g32p_row03_traceSegment_101_1890_0033, g32p_row03_traceSegment_101_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1957 8 9, g32p_row03_traceSegment_101_1957_0008, g32p_row03_traceSegment_101_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1974 8 9, g32p_row03_traceSegment_101_1974_0008, g32p_row03_traceSegment_101_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1957 17 17, g32p_row03_traceSegment_101_1957_0017, g32p_row03_traceSegment_101_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1991 8 9, g32p_row03_traceSegment_101_1991_0008, g32p_row03_traceSegment_101_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2008 8 9, g32p_row03_traceSegment_101_2008_0008, g32p_row03_traceSegment_101_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1991 17 17, g32p_row03_traceSegment_101_1991_0017, g32p_row03_traceSegment_101_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1957 34 34, g32p_row03_traceSegment_101_1957_0034, g32p_row03_traceSegment_101_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1890 67 68, g32p_row03_traceSegment_101_1890_0067, g32p_row03_traceSegment_101_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2041 8 9, g32p_row03_traceSegment_101_2041_0008, g32p_row03_traceSegment_101_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2025 16 17, g32p_row03_traceSegment_101_2025_0016, g32p_row03_traceSegment_101_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2058 8 9, g32p_row03_traceSegment_101_2058_0008, g32p_row03_traceSegment_101_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2075 8 9, g32p_row03_traceSegment_101_2075_0008, g32p_row03_traceSegment_101_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2058 17 17, g32p_row03_traceSegment_101_2058_0017, g32p_row03_traceSegment_101_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2025 33 34, g32p_row03_traceSegment_101_2025_0033, g32p_row03_traceSegment_101_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2092 8 9, g32p_row03_traceSegment_101_2092_0008, g32p_row03_traceSegment_101_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2109 8 9, g32p_row03_traceSegment_101_2109_0008, g32p_row03_traceSegment_101_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2092 17 17, g32p_row03_traceSegment_101_2092_0017, g32p_row03_traceSegment_101_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2126 8 9, g32p_row03_traceSegment_101_2126_0008, g32p_row03_traceSegment_101_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2143 8 9, g32p_row03_traceSegment_101_2143_0008, g32p_row03_traceSegment_101_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2126 17 17, g32p_row03_traceSegment_101_2126_0017, g32p_row03_traceSegment_101_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2092 34 34, g32p_row03_traceSegment_101_2092_0034, g32p_row03_traceSegment_101_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2025 67 68, g32p_row03_traceSegment_101_2025_0067, g32p_row03_traceSegment_101_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 1890 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1890 135 135, g32p_row03_traceSegment_101_1890_0135, g32p_row03_traceSegment_101_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_101 1620 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1620 270 270, g32p_row03_traceSegment_101_1620_0270, g32p_row03_traceSegment_101_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_101_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_101 1080 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 1080 540 540, g32p_row03_traceSegment_101_1080_0540, g32p_row03_traceSegment_101_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_101 0 2160 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 0 1080 1080, g32p_row03_traceSegment_101_0000_1080, g32p_row03_traceSegment_101_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2176 8 9, g32p_row03_traceSegment_101_2176_0008, g32p_row03_traceSegment_101_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2160 16 17, g32p_row03_traceSegment_101_2160_0016, g32p_row03_traceSegment_101_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2193 8 9, g32p_row03_traceSegment_101_2193_0008, g32p_row03_traceSegment_101_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2210 8 9, g32p_row03_traceSegment_101_2210_0008, g32p_row03_traceSegment_101_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2193 17 17, g32p_row03_traceSegment_101_2193_0017, g32p_row03_traceSegment_101_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2160 33 34, g32p_row03_traceSegment_101_2160_0033, g32p_row03_traceSegment_101_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2227 8 9, g32p_row03_traceSegment_101_2227_0008, g32p_row03_traceSegment_101_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2244 8 9, g32p_row03_traceSegment_101_2244_0008, g32p_row03_traceSegment_101_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2227 17 17, g32p_row03_traceSegment_101_2227_0017, g32p_row03_traceSegment_101_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2261 8 9, g32p_row03_traceSegment_101_2261_0008, g32p_row03_traceSegment_101_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2278 8 9, g32p_row03_traceSegment_101_2278_0008, g32p_row03_traceSegment_101_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2261 17 17, g32p_row03_traceSegment_101_2261_0017, g32p_row03_traceSegment_101_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2227 34 34, g32p_row03_traceSegment_101_2227_0034, g32p_row03_traceSegment_101_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2160 67 68, g32p_row03_traceSegment_101_2160_0067, g32p_row03_traceSegment_101_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2311 8 9, g32p_row03_traceSegment_101_2311_0008, g32p_row03_traceSegment_101_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2295 16 17, g32p_row03_traceSegment_101_2295_0016, g32p_row03_traceSegment_101_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2328 8 9, g32p_row03_traceSegment_101_2328_0008, g32p_row03_traceSegment_101_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2345 8 9, g32p_row03_traceSegment_101_2345_0008, g32p_row03_traceSegment_101_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2328 17 17, g32p_row03_traceSegment_101_2328_0017, g32p_row03_traceSegment_101_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2295 33 34, g32p_row03_traceSegment_101_2295_0033, g32p_row03_traceSegment_101_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2362 8 9, g32p_row03_traceSegment_101_2362_0008, g32p_row03_traceSegment_101_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2379 8 9, g32p_row03_traceSegment_101_2379_0008, g32p_row03_traceSegment_101_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2362 17 17, g32p_row03_traceSegment_101_2362_0017, g32p_row03_traceSegment_101_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2396 8 9, g32p_row03_traceSegment_101_2396_0008, g32p_row03_traceSegment_101_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2413 8 9, g32p_row03_traceSegment_101_2413_0008, g32p_row03_traceSegment_101_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2396 17 17, g32p_row03_traceSegment_101_2396_0017, g32p_row03_traceSegment_101_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2362 34 34, g32p_row03_traceSegment_101_2362_0034, g32p_row03_traceSegment_101_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2295 67 68, g32p_row03_traceSegment_101_2295_0067, g32p_row03_traceSegment_101_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 2160 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2160 135 135, g32p_row03_traceSegment_101_2160_0135, g32p_row03_traceSegment_101_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2446 8 9, g32p_row03_traceSegment_101_2446_0008, g32p_row03_traceSegment_101_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2430 16 17, g32p_row03_traceSegment_101_2430_0016, g32p_row03_traceSegment_101_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2463 8 9, g32p_row03_traceSegment_101_2463_0008, g32p_row03_traceSegment_101_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2480 8 9, g32p_row03_traceSegment_101_2480_0008, g32p_row03_traceSegment_101_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2463 17 17, g32p_row03_traceSegment_101_2463_0017, g32p_row03_traceSegment_101_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2430 33 34, g32p_row03_traceSegment_101_2430_0033, g32p_row03_traceSegment_101_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2497 8 9, g32p_row03_traceSegment_101_2497_0008, g32p_row03_traceSegment_101_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2514 8 9, g32p_row03_traceSegment_101_2514_0008, g32p_row03_traceSegment_101_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2497 17 17, g32p_row03_traceSegment_101_2497_0017, g32p_row03_traceSegment_101_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2531 8 9, g32p_row03_traceSegment_101_2531_0008, g32p_row03_traceSegment_101_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2548 8 9, g32p_row03_traceSegment_101_2548_0008, g32p_row03_traceSegment_101_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2531 17 17, g32p_row03_traceSegment_101_2531_0017, g32p_row03_traceSegment_101_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2497 34 34, g32p_row03_traceSegment_101_2497_0034, g32p_row03_traceSegment_101_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2430 67 68, g32p_row03_traceSegment_101_2430_0067, g32p_row03_traceSegment_101_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2581 8 9, g32p_row03_traceSegment_101_2581_0008, g32p_row03_traceSegment_101_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2565 16 17, g32p_row03_traceSegment_101_2565_0016, g32p_row03_traceSegment_101_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2598 8 9, g32p_row03_traceSegment_101_2598_0008, g32p_row03_traceSegment_101_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2615 8 9, g32p_row03_traceSegment_101_2615_0008, g32p_row03_traceSegment_101_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2598 17 17, g32p_row03_traceSegment_101_2598_0017, g32p_row03_traceSegment_101_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2565 33 34, g32p_row03_traceSegment_101_2565_0033, g32p_row03_traceSegment_101_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2632 8 9, g32p_row03_traceSegment_101_2632_0008, g32p_row03_traceSegment_101_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2649 8 9, g32p_row03_traceSegment_101_2649_0008, g32p_row03_traceSegment_101_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2632 17 17, g32p_row03_traceSegment_101_2632_0017, g32p_row03_traceSegment_101_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2666 8 9, g32p_row03_traceSegment_101_2666_0008, g32p_row03_traceSegment_101_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2683 8 9, g32p_row03_traceSegment_101_2683_0008, g32p_row03_traceSegment_101_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2666 17 17, g32p_row03_traceSegment_101_2666_0017, g32p_row03_traceSegment_101_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2632 34 34, g32p_row03_traceSegment_101_2632_0034, g32p_row03_traceSegment_101_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2565 67 68, g32p_row03_traceSegment_101_2565_0067, g32p_row03_traceSegment_101_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2430 135 135, g32p_row03_traceSegment_101_2430_0135, g32p_row03_traceSegment_101_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_101 2160 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2160 270 270, g32p_row03_traceSegment_101_2160_0270, g32p_row03_traceSegment_101_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2716 8 9, g32p_row03_traceSegment_101_2716_0008, g32p_row03_traceSegment_101_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2700 16 17, g32p_row03_traceSegment_101_2700_0016, g32p_row03_traceSegment_101_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2733 8 9, g32p_row03_traceSegment_101_2733_0008, g32p_row03_traceSegment_101_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2750 8 9, g32p_row03_traceSegment_101_2750_0008, g32p_row03_traceSegment_101_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2733 17 17, g32p_row03_traceSegment_101_2733_0017, g32p_row03_traceSegment_101_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2700 33 34, g32p_row03_traceSegment_101_2700_0033, g32p_row03_traceSegment_101_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2767 8 9, g32p_row03_traceSegment_101_2767_0008, g32p_row03_traceSegment_101_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2784 8 9, g32p_row03_traceSegment_101_2784_0008, g32p_row03_traceSegment_101_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2767 17 17, g32p_row03_traceSegment_101_2767_0017, g32p_row03_traceSegment_101_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2801 8 9, g32p_row03_traceSegment_101_2801_0008, g32p_row03_traceSegment_101_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2818 8 9, g32p_row03_traceSegment_101_2818_0008, g32p_row03_traceSegment_101_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2801 17 17, g32p_row03_traceSegment_101_2801_0017, g32p_row03_traceSegment_101_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2767 34 34, g32p_row03_traceSegment_101_2767_0034, g32p_row03_traceSegment_101_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2700 67 68, g32p_row03_traceSegment_101_2700_0067, g32p_row03_traceSegment_101_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2851 8 9, g32p_row03_traceSegment_101_2851_0008, g32p_row03_traceSegment_101_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2835 16 17, g32p_row03_traceSegment_101_2835_0016, g32p_row03_traceSegment_101_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2868 8 9, g32p_row03_traceSegment_101_2868_0008, g32p_row03_traceSegment_101_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2885 8 9, g32p_row03_traceSegment_101_2885_0008, g32p_row03_traceSegment_101_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2868 17 17, g32p_row03_traceSegment_101_2868_0017, g32p_row03_traceSegment_101_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2835 33 34, g32p_row03_traceSegment_101_2835_0033, g32p_row03_traceSegment_101_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2902 8 9, g32p_row03_traceSegment_101_2902_0008, g32p_row03_traceSegment_101_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2919 8 9, g32p_row03_traceSegment_101_2919_0008, g32p_row03_traceSegment_101_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2902 17 17, g32p_row03_traceSegment_101_2902_0017, g32p_row03_traceSegment_101_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2936 8 9, g32p_row03_traceSegment_101_2936_0008, g32p_row03_traceSegment_101_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2953 8 9, g32p_row03_traceSegment_101_2953_0008, g32p_row03_traceSegment_101_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2936 17 17, g32p_row03_traceSegment_101_2936_0017, g32p_row03_traceSegment_101_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2902 34 34, g32p_row03_traceSegment_101_2902_0034, g32p_row03_traceSegment_101_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2835 67 68, g32p_row03_traceSegment_101_2835_0067, g32p_row03_traceSegment_101_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2700 135 135, g32p_row03_traceSegment_101_2700_0135, g32p_row03_traceSegment_101_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2986 8 9, g32p_row03_traceSegment_101_2986_0008, g32p_row03_traceSegment_101_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2970 16 17, g32p_row03_traceSegment_101_2970_0016, g32p_row03_traceSegment_101_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3003 8 9, g32p_row03_traceSegment_101_3003_0008, g32p_row03_traceSegment_101_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3020 8 9, g32p_row03_traceSegment_101_3020_0008, g32p_row03_traceSegment_101_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3003 17 17, g32p_row03_traceSegment_101_3003_0017, g32p_row03_traceSegment_101_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2970 33 34, g32p_row03_traceSegment_101_2970_0033, g32p_row03_traceSegment_101_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3037 8 9, g32p_row03_traceSegment_101_3037_0008, g32p_row03_traceSegment_101_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3054 8 9, g32p_row03_traceSegment_101_3054_0008, g32p_row03_traceSegment_101_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3037 17 17, g32p_row03_traceSegment_101_3037_0017, g32p_row03_traceSegment_101_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3071 8 9, g32p_row03_traceSegment_101_3071_0008, g32p_row03_traceSegment_101_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3088 8 9, g32p_row03_traceSegment_101_3088_0008, g32p_row03_traceSegment_101_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3071 17 17, g32p_row03_traceSegment_101_3071_0017, g32p_row03_traceSegment_101_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3037 34 34, g32p_row03_traceSegment_101_3037_0034, g32p_row03_traceSegment_101_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2970 67 68, g32p_row03_traceSegment_101_2970_0067, g32p_row03_traceSegment_101_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3121 8 9, g32p_row03_traceSegment_101_3121_0008, g32p_row03_traceSegment_101_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3105 16 17, g32p_row03_traceSegment_101_3105_0016, g32p_row03_traceSegment_101_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3138 8 9, g32p_row03_traceSegment_101_3138_0008, g32p_row03_traceSegment_101_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3155 8 9, g32p_row03_traceSegment_101_3155_0008, g32p_row03_traceSegment_101_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3138 17 17, g32p_row03_traceSegment_101_3138_0017, g32p_row03_traceSegment_101_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3105 33 34, g32p_row03_traceSegment_101_3105_0033, g32p_row03_traceSegment_101_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3172 8 9, g32p_row03_traceSegment_101_3172_0008, g32p_row03_traceSegment_101_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3189 8 9, g32p_row03_traceSegment_101_3189_0008, g32p_row03_traceSegment_101_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3172 17 17, g32p_row03_traceSegment_101_3172_0017, g32p_row03_traceSegment_101_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3206 8 9, g32p_row03_traceSegment_101_3206_0008, g32p_row03_traceSegment_101_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3223 8 9, g32p_row03_traceSegment_101_3223_0008, g32p_row03_traceSegment_101_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3206 17 17, g32p_row03_traceSegment_101_3206_0017, g32p_row03_traceSegment_101_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3172 34 34, g32p_row03_traceSegment_101_3172_0034, g32p_row03_traceSegment_101_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3105 67 68, g32p_row03_traceSegment_101_3105_0067, g32p_row03_traceSegment_101_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2970 135 135, g32p_row03_traceSegment_101_2970_0135, g32p_row03_traceSegment_101_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_101 2700 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2700 270 270, g32p_row03_traceSegment_101_2700_0270, g32p_row03_traceSegment_101_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_101 2160 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2160 540 540, g32p_row03_traceSegment_101_2160_0540, g32p_row03_traceSegment_101_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3256 8 9, g32p_row03_traceSegment_101_3256_0008, g32p_row03_traceSegment_101_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3240 16 17, g32p_row03_traceSegment_101_3240_0016, g32p_row03_traceSegment_101_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3273 8 9, g32p_row03_traceSegment_101_3273_0008, g32p_row03_traceSegment_101_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3290 8 9, g32p_row03_traceSegment_101_3290_0008, g32p_row03_traceSegment_101_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3273 17 17, g32p_row03_traceSegment_101_3273_0017, g32p_row03_traceSegment_101_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3240 33 34, g32p_row03_traceSegment_101_3240_0033, g32p_row03_traceSegment_101_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3307 8 9, g32p_row03_traceSegment_101_3307_0008, g32p_row03_traceSegment_101_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3324 8 9, g32p_row03_traceSegment_101_3324_0008, g32p_row03_traceSegment_101_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3307 17 17, g32p_row03_traceSegment_101_3307_0017, g32p_row03_traceSegment_101_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3341 8 9, g32p_row03_traceSegment_101_3341_0008, g32p_row03_traceSegment_101_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3358 8 9, g32p_row03_traceSegment_101_3358_0008, g32p_row03_traceSegment_101_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3341 17 17, g32p_row03_traceSegment_101_3341_0017, g32p_row03_traceSegment_101_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3307 34 34, g32p_row03_traceSegment_101_3307_0034, g32p_row03_traceSegment_101_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3240 67 68, g32p_row03_traceSegment_101_3240_0067, g32p_row03_traceSegment_101_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3391 8 9, g32p_row03_traceSegment_101_3391_0008, g32p_row03_traceSegment_101_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3375 16 17, g32p_row03_traceSegment_101_3375_0016, g32p_row03_traceSegment_101_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3408 8 9, g32p_row03_traceSegment_101_3408_0008, g32p_row03_traceSegment_101_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3425 8 9, g32p_row03_traceSegment_101_3425_0008, g32p_row03_traceSegment_101_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3408 17 17, g32p_row03_traceSegment_101_3408_0017, g32p_row03_traceSegment_101_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3375 33 34, g32p_row03_traceSegment_101_3375_0033, g32p_row03_traceSegment_101_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3442 8 9, g32p_row03_traceSegment_101_3442_0008, g32p_row03_traceSegment_101_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3459 8 9, g32p_row03_traceSegment_101_3459_0008, g32p_row03_traceSegment_101_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3442 17 17, g32p_row03_traceSegment_101_3442_0017, g32p_row03_traceSegment_101_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3476 8 9, g32p_row03_traceSegment_101_3476_0008, g32p_row03_traceSegment_101_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3493 8 9, g32p_row03_traceSegment_101_3493_0008, g32p_row03_traceSegment_101_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3476 17 17, g32p_row03_traceSegment_101_3476_0017, g32p_row03_traceSegment_101_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3442 34 34, g32p_row03_traceSegment_101_3442_0034, g32p_row03_traceSegment_101_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3375 67 68, g32p_row03_traceSegment_101_3375_0067, g32p_row03_traceSegment_101_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3240 135 135, g32p_row03_traceSegment_101_3240_0135, g32p_row03_traceSegment_101_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3526 8 9, g32p_row03_traceSegment_101_3526_0008, g32p_row03_traceSegment_101_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3510 16 17, g32p_row03_traceSegment_101_3510_0016, g32p_row03_traceSegment_101_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3543 8 9, g32p_row03_traceSegment_101_3543_0008, g32p_row03_traceSegment_101_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3560 8 9, g32p_row03_traceSegment_101_3560_0008, g32p_row03_traceSegment_101_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3543 17 17, g32p_row03_traceSegment_101_3543_0017, g32p_row03_traceSegment_101_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3510 33 34, g32p_row03_traceSegment_101_3510_0033, g32p_row03_traceSegment_101_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3577 8 9, g32p_row03_traceSegment_101_3577_0008, g32p_row03_traceSegment_101_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3594 8 9, g32p_row03_traceSegment_101_3594_0008, g32p_row03_traceSegment_101_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3577 17 17, g32p_row03_traceSegment_101_3577_0017, g32p_row03_traceSegment_101_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3611 8 9, g32p_row03_traceSegment_101_3611_0008, g32p_row03_traceSegment_101_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3628 8 9, g32p_row03_traceSegment_101_3628_0008, g32p_row03_traceSegment_101_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3611 17 17, g32p_row03_traceSegment_101_3611_0017, g32p_row03_traceSegment_101_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3577 34 34, g32p_row03_traceSegment_101_3577_0034, g32p_row03_traceSegment_101_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3510 67 68, g32p_row03_traceSegment_101_3510_0067, g32p_row03_traceSegment_101_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3661 8 9, g32p_row03_traceSegment_101_3661_0008, g32p_row03_traceSegment_101_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3645 16 17, g32p_row03_traceSegment_101_3645_0016, g32p_row03_traceSegment_101_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3678 8 9, g32p_row03_traceSegment_101_3678_0008, g32p_row03_traceSegment_101_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3695 8 9, g32p_row03_traceSegment_101_3695_0008, g32p_row03_traceSegment_101_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3678 17 17, g32p_row03_traceSegment_101_3678_0017, g32p_row03_traceSegment_101_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3645 33 34, g32p_row03_traceSegment_101_3645_0033, g32p_row03_traceSegment_101_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3712 8 9, g32p_row03_traceSegment_101_3712_0008, g32p_row03_traceSegment_101_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3729 8 9, g32p_row03_traceSegment_101_3729_0008, g32p_row03_traceSegment_101_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3712 17 17, g32p_row03_traceSegment_101_3712_0017, g32p_row03_traceSegment_101_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3746 8 9, g32p_row03_traceSegment_101_3746_0008, g32p_row03_traceSegment_101_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3763 8 9, g32p_row03_traceSegment_101_3763_0008, g32p_row03_traceSegment_101_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3746 17 17, g32p_row03_traceSegment_101_3746_0017, g32p_row03_traceSegment_101_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3712 34 34, g32p_row03_traceSegment_101_3712_0034, g32p_row03_traceSegment_101_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3645 67 68, g32p_row03_traceSegment_101_3645_0067, g32p_row03_traceSegment_101_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 3510 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3510 135 135, g32p_row03_traceSegment_101_3510_0135, g32p_row03_traceSegment_101_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_101 3240 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3240 270 270, g32p_row03_traceSegment_101_3240_0270, g32p_row03_traceSegment_101_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3796 8 9, g32p_row03_traceSegment_101_3796_0008, g32p_row03_traceSegment_101_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3780 16 17, g32p_row03_traceSegment_101_3780_0016, g32p_row03_traceSegment_101_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3813 8 9, g32p_row03_traceSegment_101_3813_0008, g32p_row03_traceSegment_101_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3830 8 9, g32p_row03_traceSegment_101_3830_0008, g32p_row03_traceSegment_101_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3813 17 17, g32p_row03_traceSegment_101_3813_0017, g32p_row03_traceSegment_101_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3780 33 34, g32p_row03_traceSegment_101_3780_0033, g32p_row03_traceSegment_101_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3847 8 9, g32p_row03_traceSegment_101_3847_0008, g32p_row03_traceSegment_101_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3864 8 9, g32p_row03_traceSegment_101_3864_0008, g32p_row03_traceSegment_101_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3847 17 17, g32p_row03_traceSegment_101_3847_0017, g32p_row03_traceSegment_101_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3881 8 9, g32p_row03_traceSegment_101_3881_0008, g32p_row03_traceSegment_101_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3898 8 9, g32p_row03_traceSegment_101_3898_0008, g32p_row03_traceSegment_101_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3881 17 17, g32p_row03_traceSegment_101_3881_0017, g32p_row03_traceSegment_101_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3847 34 34, g32p_row03_traceSegment_101_3847_0034, g32p_row03_traceSegment_101_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3780 67 68, g32p_row03_traceSegment_101_3780_0067, g32p_row03_traceSegment_101_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3931 8 9, g32p_row03_traceSegment_101_3931_0008, g32p_row03_traceSegment_101_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3915 16 17, g32p_row03_traceSegment_101_3915_0016, g32p_row03_traceSegment_101_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3948 8 9, g32p_row03_traceSegment_101_3948_0008, g32p_row03_traceSegment_101_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3965 8 9, g32p_row03_traceSegment_101_3965_0008, g32p_row03_traceSegment_101_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3948 17 17, g32p_row03_traceSegment_101_3948_0017, g32p_row03_traceSegment_101_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3915 33 34, g32p_row03_traceSegment_101_3915_0033, g32p_row03_traceSegment_101_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3982 8 9, g32p_row03_traceSegment_101_3982_0008, g32p_row03_traceSegment_101_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3999 8 9, g32p_row03_traceSegment_101_3999_0008, g32p_row03_traceSegment_101_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3982 17 17, g32p_row03_traceSegment_101_3982_0017, g32p_row03_traceSegment_101_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4016 8 9, g32p_row03_traceSegment_101_4016_0008, g32p_row03_traceSegment_101_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4033 8 9, g32p_row03_traceSegment_101_4033_0008, g32p_row03_traceSegment_101_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4016 17 17, g32p_row03_traceSegment_101_4016_0017, g32p_row03_traceSegment_101_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3982 34 34, g32p_row03_traceSegment_101_3982_0034, g32p_row03_traceSegment_101_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3915 67 68, g32p_row03_traceSegment_101_3915_0067, g32p_row03_traceSegment_101_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3780 135 135, g32p_row03_traceSegment_101_3780_0135, g32p_row03_traceSegment_101_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4066 8 9, g32p_row03_traceSegment_101_4066_0008, g32p_row03_traceSegment_101_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4050 16 17, g32p_row03_traceSegment_101_4050_0016, g32p_row03_traceSegment_101_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4083 8 9, g32p_row03_traceSegment_101_4083_0008, g32p_row03_traceSegment_101_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4100 8 9, g32p_row03_traceSegment_101_4100_0008, g32p_row03_traceSegment_101_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4083 17 17, g32p_row03_traceSegment_101_4083_0017, g32p_row03_traceSegment_101_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4050 33 34, g32p_row03_traceSegment_101_4050_0033, g32p_row03_traceSegment_101_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4117 8 9, g32p_row03_traceSegment_101_4117_0008, g32p_row03_traceSegment_101_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4134 8 9, g32p_row03_traceSegment_101_4134_0008, g32p_row03_traceSegment_101_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4117 17 17, g32p_row03_traceSegment_101_4117_0017, g32p_row03_traceSegment_101_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4151 8 9, g32p_row03_traceSegment_101_4151_0008, g32p_row03_traceSegment_101_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4168 8 9, g32p_row03_traceSegment_101_4168_0008, g32p_row03_traceSegment_101_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4151 17 17, g32p_row03_traceSegment_101_4151_0017, g32p_row03_traceSegment_101_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4117 34 34, g32p_row03_traceSegment_101_4117_0034, g32p_row03_traceSegment_101_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4050 67 68, g32p_row03_traceSegment_101_4050_0067, g32p_row03_traceSegment_101_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_101 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4201 8 9, g32p_row03_traceSegment_101_4201_0008, g32p_row03_traceSegment_101_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_101 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4185 16 17, g32p_row03_traceSegment_101_4185_0016, g32p_row03_traceSegment_101_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4218 8 9, g32p_row03_traceSegment_101_4218_0008, g32p_row03_traceSegment_101_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4235 8 9, g32p_row03_traceSegment_101_4235_0008, g32p_row03_traceSegment_101_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4218 17 17, g32p_row03_traceSegment_101_4218_0017, g32p_row03_traceSegment_101_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_101 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4185 33 34, g32p_row03_traceSegment_101_4185_0033, g32p_row03_traceSegment_101_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4252 8 9, g32p_row03_traceSegment_101_4252_0008, g32p_row03_traceSegment_101_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4269 8 9, g32p_row03_traceSegment_101_4269_0008, g32p_row03_traceSegment_101_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4252 17 17, g32p_row03_traceSegment_101_4252_0017, g32p_row03_traceSegment_101_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4286 8 9, g32p_row03_traceSegment_101_4286_0008, g32p_row03_traceSegment_101_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_101 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_101 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_101_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_101 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4303 8 9, g32p_row03_traceSegment_101_4303_0008, g32p_row03_traceSegment_101_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_101 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4286 17 17, g32p_row03_traceSegment_101_4286_0017, g32p_row03_traceSegment_101_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_101 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4252 34 34, g32p_row03_traceSegment_101_4252_0034, g32p_row03_traceSegment_101_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_101 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4185 67 68, g32p_row03_traceSegment_101_4185_0067, g32p_row03_traceSegment_101_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_101_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_101 4050 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 4050 135 135, g32p_row03_traceSegment_101_4050_0135, g32p_row03_traceSegment_101_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_101 3780 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3780 270 270, g32p_row03_traceSegment_101_3780_0270, g32p_row03_traceSegment_101_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_101_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_101 3240 1080 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 3240 540 540, g32p_row03_traceSegment_101_3240_0540, g32p_row03_traceSegment_101_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_101_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_101 2160 2160 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 2160 1080 1080, g32p_row03_traceSegment_101_2160_1080, g32p_row03_traceSegment_101_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_101_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_101 0 4320 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_101 0 2160 2160, g32p_row03_traceSegment_101_0000_2160, g32p_row03_traceSegment_101_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_101_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 99) (g32p_literalTraceValue 2 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row03_traceCoefficients_099]
  decide +kernel

theorem g32p_row03_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 101) (g32p_literalTraceValue 2 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row03_traceCoefficients_101]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row03_generatorIndex : Fin 8 → Fin 408 :=
  ![2, 53, 104, 155, 208, 209, 310, 311]

theorem g32p_row03_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup01_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 2 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 2 g32p_row03_supplierClass
    g32p_row03_supplierClass_isConj g32p_supplierGroup01_support g32p_row03_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row03_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup01_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row03_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 2 c false (g32p_row03_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 2 c true (g32p_row03_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 2 c false (g32p_row03_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 2 c true (g32p_row03_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 2 c false (g32p_row03_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 2 c false (g32p_row03_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 2 c true (g32p_row03_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 2 c true (g32p_row03_coinduced_zero c hc true) 3

theorem g32p_row03_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup01_support →
      g32p_literalTraceValue (g32p_row03_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row03_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup01_support →
      g32p_literalTraceValue (g32p_row03_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row03_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup01_support →
      g32p_literalTraceValue (g32p_row03_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row03_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup01_support →
      g32p_literalTraceValue (g32p_row03_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row03_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup01_support →
      g32p_literalTraceValue (g32p_row03_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row03_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup01_support →
      g32p_literalTraceValue (g32p_row03_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row03_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup01_support →
      g32p_literalTraceValue (g32p_row03_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row03_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup01_support) :
    g32p_literalTraceValue (g32p_row03_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup01_support →
    g32p_literalTraceValue (g32p_row03_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row03_zeroTrace_block_00 r k
  · exact g32p_row03_zeroTrace_block_01 r k
  · exact g32p_row03_zeroTrace_block_02 r k
  · exact g32p_row03_zeroTrace_block_03 r k
  · exact g32p_row03_zeroTrace_block_04 r k
  · exact g32p_row03_zeroTrace_block_05 r k
  · exact g32p_row03_zeroTrace_block_06 r k

theorem g32p_row03_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup01_support) :
    (g32p_recordedInductionGenerators (g32p_row03_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row03_generatorIndex k) c) := by
  rw [g32p_row03_recordedGenerator_zero c hc k, g32p_row03_zeroTrace_arithmetic c k hc]
  norm_num [HurwitzPrymRex_ev]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def g32p_row03_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [25920, 25920, 25920] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [0, 0, 12960, 12960] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 8640, 8640] else [])) else (if i.val < 16 then [-12960] else (if i.val < 17 then [4320, 4320, 4320] else []))) else (if i.val < 21 then (if i.val < 19 then [51840, 51840] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [8640, 8640] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else [-8640]))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [12960, 12960, 12960] else [])) else (if i.val < 36 then (if i.val < 35 then [17280, 25920, 25920] else [12960, 12960, 12960]) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [4320, 4320] else (if i.val < 40 then [] else [12960, 12960])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [0, 0, 8640, 8640])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [0, 0, 4320, 4320] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [0, 4320, 4320] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [4320, 4320, 4320] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [-51840])) else (if i.val < 67 then [-12960] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [8640, 8640] else (if i.val < 71 then [] else [12960, 12960])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [0, 0, 51840, 51840] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else [0, 0, 12960, 12960]) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [25920, 25920, 25920] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row03_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup01_support) :
    g32p_supplierTracePolynomialCheck 4320 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) c) (g32p_literalTraceValue 2 c)
      [1, -1, 1] (g32p_row03_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row03_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_010
  · exact g32p_row03_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_015
  · exact g32p_row03_tracePolynomial_016
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_021
  · exact g32p_row03_tracePolynomial_022
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_026
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_030
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_034
  · exact g32p_row03_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_037
  · exact g32p_row03_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_040
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_045
  · exact g32p_row03_tracePolynomial_046
  · exact g32p_row03_tracePolynomial_047
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_049
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_056
  · exact g32p_row03_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_060
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_065
  · exact g32p_row03_tracePolynomial_066
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_071
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_073
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_075
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_086
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_092
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_096
  · exact g32p_row03_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup01_support) hc)
  · exact g32p_row03_tracePolynomial_101

theorem g32p_row03_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 2 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 2 c) := by
  by_cases hc : c ∈ g32p_supplierGroup01_support
  · have hclass (j : Fin 4320) :
        IsConj (g32p_literalRepresentative c) (g32p_row03_groupEquiv j : g32p_G) ↔
          g32p_row03_supplierClassifier j = c := by
      simpa only [g32p_row03_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row03_supplierClass_iff (g32p_row03_groupEquiv j) c
    have hχ (j : Fin 4320) :
        (g32p_recordedSupplierCharacters 2 (g32p_row03_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row03_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 2 (show (g32p_recordedSuppliers 2).H from g32p_row03_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row03_characterValues (g32p_row03_groupEquiv.symm (g32p_row03_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 2).H (g32p_recordedSupplierCharacters 2)
      (g32p_literalRepresentative c) g32p_row03_groupEquiv g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) c 6 4320
      (g32p_literalCentralizer c) (g32p_literalTraceValue 2 c) [1, -1, 1]
      (g32p_row03_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row03_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 2)))
      (g32p_row03_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row03_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row03_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row03_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row03_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row03_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row03_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row03_variantArithmetic_00_0 r
  · exact g32p_row03_variantArithmetic_01_0 r
  · exact g32p_row03_variantArithmetic_02_0 r
  · exact g32p_row03_variantArithmetic_03_0 r
  · exact g32p_row03_variantArithmetic_04_0 r
  · exact g32p_row03_variantArithmetic_05_0 r
  · exact g32p_row03_variantArithmetic_06_0 r

theorem g32p_row03_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row03_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row03_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row03_variantArithmetic_00_1 r
  · exact g32p_row03_variantArithmetic_01_1 r
  · exact g32p_row03_variantArithmetic_02_1 r
  · exact g32p_row03_variantArithmetic_03_1 r
  · exact g32p_row03_variantArithmetic_04_1 r
  · exact g32p_row03_variantArithmetic_05_1 r
  · exact g32p_row03_variantArithmetic_06_1 r

theorem g32p_row03_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row03_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row03_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row03_variantArithmetic_00_2 r
  · exact g32p_row03_variantArithmetic_01_2 r
  · exact g32p_row03_variantArithmetic_02_2 r
  · exact g32p_row03_variantArithmetic_03_2 r
  · exact g32p_row03_variantArithmetic_04_2 r
  · exact g32p_row03_variantArithmetic_05_2 r
  · exact g32p_row03_variantArithmetic_06_2 r

theorem g32p_row03_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row03_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row03_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row03_variantArithmetic_00_3 r
  · exact g32p_row03_variantArithmetic_01_3 r
  · exact g32p_row03_variantArithmetic_02_3 r
  · exact g32p_row03_variantArithmetic_03_3 r
  · exact g32p_row03_variantArithmetic_04_3 r
  · exact g32p_row03_variantArithmetic_05_3 r
  · exact g32p_row03_variantArithmetic_06_3 r

theorem g32p_row03_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row03_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row03_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row03_variantArithmetic_00_4 r
  · exact g32p_row03_variantArithmetic_01_4 r
  · exact g32p_row03_variantArithmetic_02_4 r
  · exact g32p_row03_variantArithmetic_03_4 r
  · exact g32p_row03_variantArithmetic_04_4 r
  · exact g32p_row03_variantArithmetic_05_4 r
  · exact g32p_row03_variantArithmetic_06_4 r

theorem g32p_row03_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row03_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row03_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row03_variantArithmetic_00_5 r
  · exact g32p_row03_variantArithmetic_01_5 r
  · exact g32p_row03_variantArithmetic_02_5 r
  · exact g32p_row03_variantArithmetic_03_5 r
  · exact g32p_row03_variantArithmetic_04_5 r
  · exact g32p_row03_variantArithmetic_05_5 r
  · exact g32p_row03_variantArithmetic_06_5 r

theorem g32p_row03_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row03_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row03_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row03_variantArithmetic_00_6 r
  · exact g32p_row03_variantArithmetic_01_6 r
  · exact g32p_row03_variantArithmetic_02_6 r
  · exact g32p_row03_variantArithmetic_03_6 r
  · exact g32p_row03_variantArithmetic_04_6 r
  · exact g32p_row03_variantArithmetic_05_6 r
  · exact g32p_row03_variantArithmetic_06_6 r

theorem g32p_row03_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row03_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row03_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 2 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row03_variantArithmetic_00_7 r
  · exact g32p_row03_variantArithmetic_01_7 r
  · exact g32p_row03_variantArithmetic_02_7 r
  · exact g32p_row03_variantArithmetic_03_7 r
  · exact g32p_row03_variantArithmetic_04_7 r
  · exact g32p_row03_variantArithmetic_05_7 r
  · exact g32p_row03_variantArithmetic_06_7 r

theorem g32p_row03_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row03_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row03_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 2 c _ (g32p_row03_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row03_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 2 c _ (g32p_row03_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row03_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 2 c _ (g32p_row03_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row03_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 2 c _ (g32p_row03_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row03_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 2 c _ (g32p_row03_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row03_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 2 c _ (g32p_row03_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row03_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 2 c _ (g32p_row03_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row03_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 2 c _ (g32p_row03_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row03_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end
