import HodgeLean.Foundations.Program.G32PropFourSixPacked0347
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0352
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0348
import HodgeLean.Foundations.Program.G32PropFourSixPacked0349
import HodgeLean.Foundations.Program.G32PropFourSixPacked0350
import HodgeLean.Foundations.Program.G32PropFourSixPacked0351
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow08
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_101_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 0 15 15, g32p_row07_traceSegment_101_0000_0015, g32p_row07_traceSegment_101_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 45 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 30 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 30 15 15, g32p_row07_traceSegment_101_0030_0015, g32p_row07_traceSegment_101_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_101 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 0 30 30, g32p_row07_traceSegment_101_0000_0030, g32p_row07_traceSegment_101_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 60 15 15, g32p_row07_traceSegment_101_0060_0015, g32p_row07_traceSegment_101_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 90 15 16, g32p_row07_traceSegment_101_0090_0015, g32p_row07_traceSegment_101_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 60 30 31, g32p_row07_traceSegment_101_0060_0030, g32p_row07_traceSegment_101_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_101 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 0 60 61, g32p_row07_traceSegment_101_0000_0060, g32p_row07_traceSegment_101_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 121 15 15, g32p_row07_traceSegment_101_0121_0015, g32p_row07_traceSegment_101_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 151 15 16, g32p_row07_traceSegment_101_0151_0015, g32p_row07_traceSegment_101_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 121 30 31, g32p_row07_traceSegment_101_0121_0030, g32p_row07_traceSegment_101_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 182 15 15, g32p_row07_traceSegment_101_0182_0015, g32p_row07_traceSegment_101_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 212 15 16, g32p_row07_traceSegment_101_0212_0015, g32p_row07_traceSegment_101_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 182 30 31, g32p_row07_traceSegment_101_0182_0030, g32p_row07_traceSegment_101_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_101 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 121 61 61, g32p_row07_traceSegment_101_0121_0061, g32p_row07_traceSegment_101_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_101 0 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 0 121 122, g32p_row07_traceSegment_101_0000_0121, g32p_row07_traceSegment_101_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 243 15 15, g32p_row07_traceSegment_101_0243_0015, g32p_row07_traceSegment_101_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 273 15 15, g32p_row07_traceSegment_101_0273_0015, g32p_row07_traceSegment_101_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_101 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 243 30 30, g32p_row07_traceSegment_101_0243_0030, g32p_row07_traceSegment_101_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 303 15 15, g32p_row07_traceSegment_101_0303_0015, g32p_row07_traceSegment_101_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 333 15 16, g32p_row07_traceSegment_101_0333_0015, g32p_row07_traceSegment_101_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 303 30 31, g32p_row07_traceSegment_101_0303_0030, g32p_row07_traceSegment_101_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_101 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 243 60 61, g32p_row07_traceSegment_101_0243_0060, g32p_row07_traceSegment_101_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 364 15 15, g32p_row07_traceSegment_101_0364_0015, g32p_row07_traceSegment_101_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 394 15 16, g32p_row07_traceSegment_101_0394_0015, g32p_row07_traceSegment_101_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 364 30 31, g32p_row07_traceSegment_101_0364_0030, g32p_row07_traceSegment_101_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 425 15 15, g32p_row07_traceSegment_101_0425_0015, g32p_row07_traceSegment_101_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 455 15 16, g32p_row07_traceSegment_101_0455_0015, g32p_row07_traceSegment_101_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 425 30 31, g32p_row07_traceSegment_101_0425_0030, g32p_row07_traceSegment_101_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_101 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 364 61 61, g32p_row07_traceSegment_101_0364_0061, g32p_row07_traceSegment_101_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_101 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 243 121 122, g32p_row07_traceSegment_101_0243_0121, g32p_row07_traceSegment_101_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_101 0 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 0 243 243, g32p_row07_traceSegment_101_0000_0243, g32p_row07_traceSegment_101_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 486 15 15, g32p_row07_traceSegment_101_0486_0015, g32p_row07_traceSegment_101_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 516 15 15, g32p_row07_traceSegment_101_0516_0015, g32p_row07_traceSegment_101_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_101 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 486 30 30, g32p_row07_traceSegment_101_0486_0030, g32p_row07_traceSegment_101_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 546 15 15, g32p_row07_traceSegment_101_0546_0015, g32p_row07_traceSegment_101_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 576 15 16, g32p_row07_traceSegment_101_0576_0015, g32p_row07_traceSegment_101_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 546 30 31, g32p_row07_traceSegment_101_0546_0030, g32p_row07_traceSegment_101_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_101 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 486 60 61, g32p_row07_traceSegment_101_0486_0060, g32p_row07_traceSegment_101_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 607 15 15, g32p_row07_traceSegment_101_0607_0015, g32p_row07_traceSegment_101_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 637 15 16, g32p_row07_traceSegment_101_0637_0015, g32p_row07_traceSegment_101_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 607 30 31, g32p_row07_traceSegment_101_0607_0030, g32p_row07_traceSegment_101_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 668 15 15, g32p_row07_traceSegment_101_0668_0015, g32p_row07_traceSegment_101_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 698 15 16, g32p_row07_traceSegment_101_0698_0015, g32p_row07_traceSegment_101_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 668 30 31, g32p_row07_traceSegment_101_0668_0030, g32p_row07_traceSegment_101_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_101 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 607 61 61, g32p_row07_traceSegment_101_0607_0061, g32p_row07_traceSegment_101_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_101 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 486 121 122, g32p_row07_traceSegment_101_0486_0121, g32p_row07_traceSegment_101_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 729 15 15, g32p_row07_traceSegment_101_0729_0015, g32p_row07_traceSegment_101_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 759 15 15, g32p_row07_traceSegment_101_0759_0015, g32p_row07_traceSegment_101_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_101 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 729 30 30, g32p_row07_traceSegment_101_0729_0030, g32p_row07_traceSegment_101_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 789 15 15, g32p_row07_traceSegment_101_0789_0015, g32p_row07_traceSegment_101_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 819 15 16, g32p_row07_traceSegment_101_0819_0015, g32p_row07_traceSegment_101_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 789 30 31, g32p_row07_traceSegment_101_0789_0030, g32p_row07_traceSegment_101_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_101 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 729 60 61, g32p_row07_traceSegment_101_0729_0060, g32p_row07_traceSegment_101_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 850 15 15, g32p_row07_traceSegment_101_0850_0015, g32p_row07_traceSegment_101_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 880 15 16, g32p_row07_traceSegment_101_0880_0015, g32p_row07_traceSegment_101_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 850 30 31, g32p_row07_traceSegment_101_0850_0030, g32p_row07_traceSegment_101_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 911 15 15, g32p_row07_traceSegment_101_0911_0015, g32p_row07_traceSegment_101_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 941 15 16, g32p_row07_traceSegment_101_0941_0015, g32p_row07_traceSegment_101_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 911 30 31, g32p_row07_traceSegment_101_0911_0030, g32p_row07_traceSegment_101_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_101 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 850 61 61, g32p_row07_traceSegment_101_0850_0061, g32p_row07_traceSegment_101_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_101 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 729 121 122, g32p_row07_traceSegment_101_0729_0121, g32p_row07_traceSegment_101_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_101 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 486 243 243, g32p_row07_traceSegment_101_0486_0243, g32p_row07_traceSegment_101_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_101 0 972 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 0 486 486, g32p_row07_traceSegment_101_0000_0486, g32p_row07_traceSegment_101_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 972 15 15, g32p_row07_traceSegment_101_0972_0015, g32p_row07_traceSegment_101_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1002 15 15, g32p_row07_traceSegment_101_1002_0015, g32p_row07_traceSegment_101_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_101 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 972 30 30, g32p_row07_traceSegment_101_0972_0030, g32p_row07_traceSegment_101_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1032 15 15, g32p_row07_traceSegment_101_1032_0015, g32p_row07_traceSegment_101_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1062 15 16, g32p_row07_traceSegment_101_1062_0015, g32p_row07_traceSegment_101_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1032 30 31, g32p_row07_traceSegment_101_1032_0030, g32p_row07_traceSegment_101_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_101 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 972 60 61, g32p_row07_traceSegment_101_0972_0060, g32p_row07_traceSegment_101_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1093 15 15, g32p_row07_traceSegment_101_1093_0015, g32p_row07_traceSegment_101_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1123 15 16, g32p_row07_traceSegment_101_1123_0015, g32p_row07_traceSegment_101_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1093 30 31, g32p_row07_traceSegment_101_1093_0030, g32p_row07_traceSegment_101_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1154 15 15, g32p_row07_traceSegment_101_1154_0015, g32p_row07_traceSegment_101_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1184 15 16, g32p_row07_traceSegment_101_1184_0015, g32p_row07_traceSegment_101_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1154 30 31, g32p_row07_traceSegment_101_1154_0030, g32p_row07_traceSegment_101_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_101 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1093 61 61, g32p_row07_traceSegment_101_1093_0061, g32p_row07_traceSegment_101_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_101 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 972 121 122, g32p_row07_traceSegment_101_0972_0121, g32p_row07_traceSegment_101_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1215 15 15, g32p_row07_traceSegment_101_1215_0015, g32p_row07_traceSegment_101_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1245 15 15, g32p_row07_traceSegment_101_1245_0015, g32p_row07_traceSegment_101_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_101 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1215 30 30, g32p_row07_traceSegment_101_1215_0030, g32p_row07_traceSegment_101_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1275 15 15, g32p_row07_traceSegment_101_1275_0015, g32p_row07_traceSegment_101_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1305 15 16, g32p_row07_traceSegment_101_1305_0015, g32p_row07_traceSegment_101_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1275 30 31, g32p_row07_traceSegment_101_1275_0030, g32p_row07_traceSegment_101_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_101 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1215 60 61, g32p_row07_traceSegment_101_1215_0060, g32p_row07_traceSegment_101_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1336 15 15, g32p_row07_traceSegment_101_1336_0015, g32p_row07_traceSegment_101_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1366 15 16, g32p_row07_traceSegment_101_1366_0015, g32p_row07_traceSegment_101_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1336 30 31, g32p_row07_traceSegment_101_1336_0030, g32p_row07_traceSegment_101_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1397 15 15, g32p_row07_traceSegment_101_1397_0015, g32p_row07_traceSegment_101_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1427 15 16, g32p_row07_traceSegment_101_1427_0015, g32p_row07_traceSegment_101_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1397 30 31, g32p_row07_traceSegment_101_1397_0030, g32p_row07_traceSegment_101_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_101 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1336 61 61, g32p_row07_traceSegment_101_1336_0061, g32p_row07_traceSegment_101_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_101 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1215 121 122, g32p_row07_traceSegment_101_1215_0121, g32p_row07_traceSegment_101_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_101 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 972 243 243, g32p_row07_traceSegment_101_0972_0243, g32p_row07_traceSegment_101_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1458 15 15, g32p_row07_traceSegment_101_1458_0015, g32p_row07_traceSegment_101_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1488 15 15, g32p_row07_traceSegment_101_1488_0015, g32p_row07_traceSegment_101_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_101 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1458 30 30, g32p_row07_traceSegment_101_1458_0030, g32p_row07_traceSegment_101_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1518 15 15, g32p_row07_traceSegment_101_1518_0015, g32p_row07_traceSegment_101_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1548 15 16, g32p_row07_traceSegment_101_1548_0015, g32p_row07_traceSegment_101_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1518 30 31, g32p_row07_traceSegment_101_1518_0030, g32p_row07_traceSegment_101_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_101 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1458 60 61, g32p_row07_traceSegment_101_1458_0060, g32p_row07_traceSegment_101_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1579 15 15, g32p_row07_traceSegment_101_1579_0015, g32p_row07_traceSegment_101_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1609 15 16, g32p_row07_traceSegment_101_1609_0015, g32p_row07_traceSegment_101_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1579 30 31, g32p_row07_traceSegment_101_1579_0030, g32p_row07_traceSegment_101_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1640 15 15, g32p_row07_traceSegment_101_1640_0015, g32p_row07_traceSegment_101_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1670 15 16, g32p_row07_traceSegment_101_1670_0015, g32p_row07_traceSegment_101_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1640 30 31, g32p_row07_traceSegment_101_1640_0030, g32p_row07_traceSegment_101_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_101 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1579 61 61, g32p_row07_traceSegment_101_1579_0061, g32p_row07_traceSegment_101_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_101 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1458 121 122, g32p_row07_traceSegment_101_1458_0121, g32p_row07_traceSegment_101_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1701 15 15, g32p_row07_traceSegment_101_1701_0015, g32p_row07_traceSegment_101_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1731 15 15, g32p_row07_traceSegment_101_1731_0015, g32p_row07_traceSegment_101_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_101 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1701 30 30, g32p_row07_traceSegment_101_1701_0030, g32p_row07_traceSegment_101_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1761 15 15, g32p_row07_traceSegment_101_1761_0015, g32p_row07_traceSegment_101_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1791 15 16, g32p_row07_traceSegment_101_1791_0015, g32p_row07_traceSegment_101_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1761 30 31, g32p_row07_traceSegment_101_1761_0030, g32p_row07_traceSegment_101_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_101 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1701 60 61, g32p_row07_traceSegment_101_1701_0060, g32p_row07_traceSegment_101_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1822 15 15, g32p_row07_traceSegment_101_1822_0015, g32p_row07_traceSegment_101_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1852 15 16, g32p_row07_traceSegment_101_1852_0015, g32p_row07_traceSegment_101_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1822 30 31, g32p_row07_traceSegment_101_1822_0030, g32p_row07_traceSegment_101_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_101 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1883 15 15, g32p_row07_traceSegment_101_1883_0015, g32p_row07_traceSegment_101_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_101 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_101 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_101_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_101 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1913 15 16, g32p_row07_traceSegment_101_1913_0015, g32p_row07_traceSegment_101_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_101 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1883 30 31, g32p_row07_traceSegment_101_1883_0030, g32p_row07_traceSegment_101_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_101 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1822 61 61, g32p_row07_traceSegment_101_1822_0061, g32p_row07_traceSegment_101_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_101 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1701 121 122, g32p_row07_traceSegment_101_1701_0121, g32p_row07_traceSegment_101_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_101_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_101 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 1458 243 243, g32p_row07_traceSegment_101_1458_0243, g32p_row07_traceSegment_101_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_101 972 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 972 486 486, g32p_row07_traceSegment_101_0972_0486, g32p_row07_traceSegment_101_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_101_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_101 0 1944 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_101 0 972 972, g32p_row07_traceSegment_101_0000_0972, g32p_row07_traceSegment_101_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 101 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_101_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row07_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 93) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 93) (g32p_literalTraceValue 6 93)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row07_traceCoefficients_093]
  decide +kernel

theorem g32p_row07_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 95) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 95) (g32p_literalTraceValue 6 95)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_095]
  decide +kernel

theorem g32p_row07_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 96) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 96) (g32p_literalTraceValue 6 96)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_096]
  decide +kernel

theorem g32p_row07_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 97) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 97) (g32p_literalTraceValue 6 97)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_097]
  decide +kernel

theorem g32p_row07_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 98) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 98) (g32p_literalTraceValue 6 98)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_098]
  decide +kernel

theorem g32p_row07_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 99) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 99) (g32p_literalTraceValue 6 99)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_099]
  decide +kernel

theorem g32p_row07_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 100) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 100) (g32p_literalTraceValue 6 100)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_100]
  decide +kernel

theorem g32p_row07_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 101) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 101) (g32p_literalTraceValue 6 101)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row07_traceCoefficients_101]
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

def g32p_row07_generatorIndex : Fin 8 → Fin 408 :=
  ![6, 57, 108, 159, 216, 217, 318, 319]

theorem g32p_row07_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup05_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 6 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 6 g32p_row07_supplierClass
    g32p_row07_supplierClass_isConj g32p_supplierGroup05_support g32p_row07_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row07_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup05_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row07_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 6 c false (g32p_row07_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 6 c true (g32p_row07_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 6 c false (g32p_row07_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 6 c true (g32p_row07_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 6 c false (g32p_row07_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 6 c false (g32p_row07_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 6 c true (g32p_row07_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 6 c true (g32p_row07_coinduced_zero c hc true) 3

theorem g32p_row07_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup05_support →
      g32p_literalTraceValue (g32p_row07_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row07_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup05_support →
      g32p_literalTraceValue (g32p_row07_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row07_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup05_support →
      g32p_literalTraceValue (g32p_row07_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row07_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup05_support →
      g32p_literalTraceValue (g32p_row07_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row07_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup05_support →
      g32p_literalTraceValue (g32p_row07_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row07_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup05_support →
      g32p_literalTraceValue (g32p_row07_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row07_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup05_support →
      g32p_literalTraceValue (g32p_row07_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row07_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup05_support) :
    g32p_literalTraceValue (g32p_row07_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup05_support →
    g32p_literalTraceValue (g32p_row07_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row07_zeroTrace_block_00 r k
  · exact g32p_row07_zeroTrace_block_01 r k
  · exact g32p_row07_zeroTrace_block_02 r k
  · exact g32p_row07_zeroTrace_block_03 r k
  · exact g32p_row07_zeroTrace_block_04 r k
  · exact g32p_row07_zeroTrace_block_05 r k
  · exact g32p_row07_zeroTrace_block_06 r k

theorem g32p_row07_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup05_support) :
    (g32p_recordedInductionGenerators (g32p_row07_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row07_generatorIndex k) c) := by
  rw [g32p_row07_recordedGenerator_zero c hc k, g32p_row07_zeroTrace_arithmetic c k hc]
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

def g32p_row07_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [15552])) else (if i.val < 4 then [] else (if i.val < 5 then [3888] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [3888])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else [3888]))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [27216] else [3888])) else (if i.val < 36 then (if i.val < 35 then [15552] else [27216]) else (if i.val < 37 then [3888] else [155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [3888])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [15552] else [15552])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [3888] else (if i.val < 94 then [15552] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520])))))))

theorem g32p_row07_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup05_support) :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) c) (g32p_literalTraceValue 6 c)
      [1, 1, 1] (g32p_row07_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row07_tracePolynomial_000
  · exact g32p_row07_tracePolynomial_001
  · exact g32p_row07_tracePolynomial_002
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_009
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_011
  · exact g32p_row07_tracePolynomial_012
  · exact g32p_row07_tracePolynomial_013
  · exact g32p_row07_tracePolynomial_014
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (18 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_030
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_032
  · exact g32p_row07_tracePolynomial_033
  · exact g32p_row07_tracePolynomial_034
  · exact g32p_row07_tracePolynomial_035
  · exact g32p_row07_tracePolynomial_036
  · exact g32p_row07_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_039
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_042
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_044
  · exact g32p_row07_tracePolynomial_045
  · exact g32p_row07_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_053
  · exact g32p_row07_tracePolynomial_054
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_062
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_067
  · exact g32p_row07_tracePolynomial_068
  · exact g32p_row07_tracePolynomial_069
  · exact g32p_row07_tracePolynomial_070
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_075
  · exact g32p_row07_tracePolynomial_076
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_087
  · exact g32p_row07_tracePolynomial_088
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_092
  · exact g32p_row07_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup05_support) hc)
  · exact g32p_row07_tracePolynomial_095
  · exact g32p_row07_tracePolynomial_096
  · exact g32p_row07_tracePolynomial_097
  · exact g32p_row07_tracePolynomial_098
  · exact g32p_row07_tracePolynomial_099
  · exact g32p_row07_tracePolynomial_100
  · exact g32p_row07_tracePolynomial_101

theorem g32p_row07_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 6 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 6 c) := by
  by_cases hc : c ∈ g32p_supplierGroup05_support
  · have hclass (j : Fin 1944) :
        IsConj (g32p_literalRepresentative c) (g32p_row07_groupEquiv j : g32p_G) ↔
          g32p_row07_supplierClassifier j = c := by
      simpa only [g32p_row07_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row07_supplierClass_iff (g32p_row07_groupEquiv j) c
    have hχ (j : Fin 1944) :
        (g32p_recordedSupplierCharacters 6 (g32p_row07_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row07_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 6 (show (g32p_recordedSuppliers 6).H from g32p_row07_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row07_characterValues (g32p_row07_groupEquiv.symm (g32p_row07_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 6).H (g32p_recordedSupplierCharacters 6)
      (g32p_literalRepresentative c) g32p_row07_groupEquiv g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) c 3 1944
      (g32p_literalCentralizer c) (g32p_literalTraceValue 6 c) [1, 1, 1]
      (g32p_row07_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row07_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 6)))
      (g32p_row07_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row07_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row07_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
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

theorem g32p_row07_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
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

theorem g32p_row07_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
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

theorem g32p_row07_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
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

theorem g32p_row07_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
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

theorem g32p_row07_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
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

theorem g32p_row07_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row07_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row07_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
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

theorem g32p_row07_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row07_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row07_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row07_variantArithmetic_00_0 r
  · exact g32p_row07_variantArithmetic_01_0 r
  · exact g32p_row07_variantArithmetic_02_0 r
  · exact g32p_row07_variantArithmetic_03_0 r
  · exact g32p_row07_variantArithmetic_04_0 r
  · exact g32p_row07_variantArithmetic_05_0 r
  · exact g32p_row07_variantArithmetic_06_0 r

theorem g32p_row07_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row07_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row07_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row07_variantArithmetic_00_1 r
  · exact g32p_row07_variantArithmetic_01_1 r
  · exact g32p_row07_variantArithmetic_02_1 r
  · exact g32p_row07_variantArithmetic_03_1 r
  · exact g32p_row07_variantArithmetic_04_1 r
  · exact g32p_row07_variantArithmetic_05_1 r
  · exact g32p_row07_variantArithmetic_06_1 r

theorem g32p_row07_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row07_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row07_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row07_variantArithmetic_00_2 r
  · exact g32p_row07_variantArithmetic_01_2 r
  · exact g32p_row07_variantArithmetic_02_2 r
  · exact g32p_row07_variantArithmetic_03_2 r
  · exact g32p_row07_variantArithmetic_04_2 r
  · exact g32p_row07_variantArithmetic_05_2 r
  · exact g32p_row07_variantArithmetic_06_2 r

theorem g32p_row07_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row07_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row07_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row07_variantArithmetic_00_3 r
  · exact g32p_row07_variantArithmetic_01_3 r
  · exact g32p_row07_variantArithmetic_02_3 r
  · exact g32p_row07_variantArithmetic_03_3 r
  · exact g32p_row07_variantArithmetic_04_3 r
  · exact g32p_row07_variantArithmetic_05_3 r
  · exact g32p_row07_variantArithmetic_06_3 r

theorem g32p_row07_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row07_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row07_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row07_variantArithmetic_00_4 r
  · exact g32p_row07_variantArithmetic_01_4 r
  · exact g32p_row07_variantArithmetic_02_4 r
  · exact g32p_row07_variantArithmetic_03_4 r
  · exact g32p_row07_variantArithmetic_04_4 r
  · exact g32p_row07_variantArithmetic_05_4 r
  · exact g32p_row07_variantArithmetic_06_4 r

theorem g32p_row07_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row07_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row07_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row07_variantArithmetic_00_5 r
  · exact g32p_row07_variantArithmetic_01_5 r
  · exact g32p_row07_variantArithmetic_02_5 r
  · exact g32p_row07_variantArithmetic_03_5 r
  · exact g32p_row07_variantArithmetic_04_5 r
  · exact g32p_row07_variantArithmetic_05_5 r
  · exact g32p_row07_variantArithmetic_06_5 r

theorem g32p_row07_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row07_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row07_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row07_variantArithmetic_00_6 r
  · exact g32p_row07_variantArithmetic_01_6 r
  · exact g32p_row07_variantArithmetic_02_6 r
  · exact g32p_row07_variantArithmetic_03_6 r
  · exact g32p_row07_variantArithmetic_04_6 r
  · exact g32p_row07_variantArithmetic_05_6 r
  · exact g32p_row07_variantArithmetic_06_6 r

theorem g32p_row07_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row07_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row07_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 6 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row07_variantArithmetic_00_7 r
  · exact g32p_row07_variantArithmetic_01_7 r
  · exact g32p_row07_variantArithmetic_02_7 r
  · exact g32p_row07_variantArithmetic_03_7 r
  · exact g32p_row07_variantArithmetic_04_7 r
  · exact g32p_row07_variantArithmetic_05_7 r
  · exact g32p_row07_variantArithmetic_06_7 r

theorem g32p_row07_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row07_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row07_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 6 c _ (g32p_row07_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row07_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 6 c _ (g32p_row07_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row07_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 6 c _ (g32p_row07_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row07_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 6 c _ (g32p_row07_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row07_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 6 c _ (g32p_row07_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row07_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 6 c _ (g32p_row07_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row07_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 6 c _ (g32p_row07_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row07_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 6 c _ (g32p_row07_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row07_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup06_source : Fin 648 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 324 then (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (80, 62)) else (if i.val < 3 then (88, 204) else (if i.val < 4 then (42, 13) else (45, 70)))) else (if i.val < 7 then (if i.val < 6 then (0, 97) else (100, 42)) else (if i.val < 8 then (48, 191) else (if i.val < 9 then (64, 199) else (24, 130))))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then (98, 20) else (20, 200)) else (if i.val < 13 then (14, 37) else (if i.val < 14 then (12, 253) else (6, 86)))) else (if i.val < 17 then (if i.val < 16 then (0, 99) else (70, 212)) else (if i.val < 18 then (41, 49) else (if i.val < 19 then (26, 118) else (111, 174)))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then (82, 169) else (92, 167)) else (if i.val < 23 then (11, 75) else (if i.val < 24 then (32, 39) else (67, 188)))) else (if i.val < 27 then (if i.val < 26 then (66, 158) else (99, 113)) else (if i.val < 28 then (50, 161) else (if i.val < 29 then (47, 7) else (138, 23))))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then (51, 199) else (107, 111)) else (if i.val < 33 then (2, 64) else (if i.val < 34 then (142, 21) else (70, 42)))) else (if i.val < 37 then (if i.val < 36 then (64, 161) else (138, 126)) else (if i.val < 38 then (125, 247) else (if i.val < 39 then (136, 98) else (7, 123))))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then (28, 10) else (138, 42)) else (if i.val < 43 then (80, 5) else (if i.val < 44 then (136, 10) else (78, 28)))) else (if i.val < 47 then (if i.val < 46 then (134, 143) else (44, 237)) else (if i.val < 48 then (122, 172) else (if i.val < 49 then (65, 212) else (99, 194))))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then (25, 125) else (106, 134)) else (if i.val < 53 then (92, 20) else (if i.val < 54 then (53, 162) else (73, 150)))) else (if i.val < 57 then (if i.val < 56 then (144, 134) else (44, 86)) else (if i.val < 58 then (63, 122) else (if i.val < 59 then (76, 64) else (82, 230)))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then (46, 43) else (113, 0)) else (if i.val < 63 then (143, 111) else (if i.val < 64 then (139, 223) else (24, 33)))) else (if i.val < 67 then (if i.val < 66 then (133, 194) else (0, 101)) else (if i.val < 68 then (91, 198) else (if i.val < 69 then (66, 77) else (25, 43))))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then (89, 15) else (9, 50)) else (if i.val < 73 then (29, 134) else (if i.val < 74 then (56, 152) else (67, 112)))) else (if i.val < 78 then (if i.val < 76 then (66, 54) else (if i.val < 77 then (0, 96) else (115, 49))) else (if i.val < 79 then (45, 220) else (if i.val < 80 then (125, 130) else (81, 224)))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then (105, 27) else (23, 69)) else (if i.val < 84 then (83, 161) else (if i.val < 85 then (61, 84) else (65, 114)))) else (if i.val < 88 then (if i.val < 87 then (100, 79) else (22, 101)) else (if i.val < 89 then (124, 105) else (if i.val < 90 then (3, 217) else (31, 201))))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then (142, 125) else (23, 103)) else (if i.val < 94 then (64, 167) else (if i.val < 95 then (107, 35) else (11, 21)))) else (if i.val < 98 then (if i.val < 97 then (141, 210) else (121, 184)) else (if i.val < 99 then (89, 115) else (if i.val < 100 then (42, 142) else (66, 164)))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then (45, 151) else (83, 197)) else (if i.val < 104 then (140, 82) else (if i.val < 105 then (28, 111) else (73, 157)))) else (if i.val < 108 then (if i.val < 107 then (54, 39) else (132, 99)) else (if i.val < 109 then (77, 116) else (if i.val < 110 then (92, 241) else (101, 223))))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then (66, 68) else (141, 37)) else (if i.val < 114 then (138, 96) else (if i.val < 115 then (127, 174) else (94, 230)))) else (if i.val < 118 then (if i.val < 117 then (76, 212) else (143, 36)) else (if i.val < 119 then (72, 103) else (if i.val < 120 then (135, 32) else (84, 33))))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then (27, 36) else (70, 176)) else (if i.val < 124 then (38, 174) else (if i.val < 125 then (31, 190) else (141, 212)))) else (if i.val < 128 then (if i.val < 127 then (85, 250) else (79, 107)) else (if i.val < 129 then (22, 25) else (if i.val < 130 then (20, 216) else (41, 221))))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then (122, 13) else (74, 225)) else (if i.val < 134 then (89, 219) else (if i.val < 135 then (118, 142) else (60, 252)))) else (if i.val < 138 then (if i.val < 137 then (60, 240) else (113, 180)) else (if i.val < 139 then (96, 221) else (if i.val < 140 then (121, 81) else (39, 96)))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then (130, 4) else (47, 13)) else (if i.val < 144 then (79, 12) else (if i.val < 145 then (116, 85) else (42, 244)))) else (if i.val < 148 then (if i.val < 147 then (48, 50) else (43, 61)) else (if i.val < 149 then (122, 16) else (if i.val < 150 then (0, 34) else (85, 113))))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then (45, 234) else (126, 154)) else (if i.val < 154 then (43, 149) else (if i.val < 155 then (15, 167) else (96, 172)))) else (if i.val < 159 then (if i.val < 157 then (142, 113) else (if i.val < 158 then (43, 83) else (137, 93))) else (if i.val < 160 then (74, 233) else (if i.val < 161 then (23, 22) else (17, 77))))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then (79, 93) else (67, 244)) else (if i.val < 165 then (43, 191) else (if i.val < 166 then (40, 253) else (51, 215)))) else (if i.val < 169 then (if i.val < 168 then (143, 152) else (103, 124)) else (if i.val < 170 then (138, 162) else (if i.val < 171 then (50, 122) else (68, 183))))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then (48, 208) else (121, 31)) else (if i.val < 175 then (71, 144) else (if i.val < 176 then (38, 132) else (37, 228)))) else (if i.val < 179 then (if i.val < 178 then (72, 219) else (36, 63)) else (if i.val < 180 then (143, 144) else (if i.val < 181 then (74, 184) else (40, 195)))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then (120, 150) else (72, 226)) else (if i.val < 185 then (63, 225) else (if i.val < 186 then (88, 5) else (84, 157)))) else (if i.val < 189 then (if i.val < 188 then (53, 173) else (61, 0)) else (if i.val < 190 then (57, 173) else (if i.val < 191 then (70, 27) else (85, 78))))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then (93, 53) else (50, 18)) else (if i.val < 195 then (127, 21) else (if i.val < 196 then (83, 28) else (86, 109)))) else (if i.val < 199 then (if i.val < 198 then (35, 152) else (121, 177)) else (if i.val < 200 then (144, 173) else (if i.val < 201 then (120, 170) else (94, 22))))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then (131, 126) else (14, 86)) else (if i.val < 205 then (114, 33) else (if i.val < 206 then (69, 3) else (11, 253)))) else (if i.val < 209 then (if i.val < 208 then (51, 98) else (144, 55)) else (if i.val < 210 then (144, 13) else (if i.val < 211 then (79, 105) else (94, 64))))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then (43, 168) else (56, 59)) else (if i.val < 215 then (115, 3) else (if i.val < 216 then (68, 18) else (117, 23)))) else (if i.val < 219 then (if i.val < 218 then (138, 59) else (55, 151)) else (if i.val < 220 then (23, 30) else (if i.val < 221 then (18, 199) else (20, 254)))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then (55, 211) else (6, 177)) else (if i.val < 225 then (29, 185) else (if i.val < 226 then (6, 155) else (36, 125)))) else (if i.val < 229 then (if i.val < 228 then (128, 226) else (73, 40)) else (if i.val < 230 then (35, 236) else (if i.val < 231 then (55, 78) else (103, 83))))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then (39, 19) else (32, 135)) else (if i.val < 235 then (117, 226) else (if i.val < 236 then (8, 99) else (92, 134)))) else (if i.val < 240 then (if i.val < 238 then (111, 90) else (if i.val < 239 then (51, 234) else (79, 255))) else (if i.val < 241 then (70, 117) else (if i.val < 242 then (25, 145) else (127, 111)))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then (50, 197) else (30, 7)) else (if i.val < 246 then (1, 165) else (if i.val < 247 then (121, 123) else (126, 82)))) else (if i.val < 250 then (if i.val < 249 then (141, 253) else (80, 43)) else (if i.val < 251 then (53, 231) else (if i.val < 252 then (125, 100) else (33, 136))))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then (111, 11) else (49, 167)) else (if i.val < 256 then (33, 68) else (if i.val < 257 then (38, 233) else (33, 80)))) else (if i.val < 260 then (if i.val < 259 then (43, 184) else (76, 181)) else (if i.val < 261 then (34, 236) else (if i.val < 262 then (66, 78) else (78, 222)))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then (125, 118) else (22, 50)) else (if i.val < 266 then (129, 227) else (if i.val < 267 then (37, 177) else (17, 146)))) else (if i.val < 270 then (if i.val < 269 then (143, 6) else (71, 4)) else (if i.val < 271 then (21, 194) else (if i.val < 272 then (137, 176) else (137, 95))))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then (39, 126) else (137, 250)) else (if i.val < 276 then (119, 142) else (if i.val < 277 then (143, 46) else (131, 96)))) else (if i.val < 280 then (if i.val < 279 then (20, 14) else (144, 205)) else (if i.val < 281 then (98, 8) else (if i.val < 282 then (92, 211) else (136, 75))))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then (32, 104) else (131, 97)) else (if i.val < 286 then (103, 219) else (if i.val < 287 then (135, 252) else (142, 73)))) else (if i.val < 290 then (if i.val < 289 then (127, 78) else (45, 208)) else (if i.val < 291 then (77, 133) else (if i.val < 292 then (76, 9) else (129, 245))))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then (7, 127) else (76, 250)) else (if i.val < 296 then (44, 183) else (if i.val < 297 then (141, 222) else (21, 123)))) else (if i.val < 300 then (if i.val < 299 then (77, 194) else (39, 0)) else (if i.val < 301 then (125, 43) else (if i.val < 302 then (28, 77) else (5, 205)))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then (17, 191) else (62, 109)) else (if i.val < 306 then (142, 80) else (if i.val < 307 then (31, 115) else (65, 74)))) else (if i.val < 310 then (if i.val < 309 then (1, 196) else (138, 242)) else (if i.val < 311 then (84, 207) else (if i.val < 312 then (71, 72) else (67, 8))))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then (78, 107) else (120, 171)) else (if i.val < 316 then (49, 99) else (if i.val < 317 then (27, 196) else (81, 78)))) else (if i.val < 321 then (if i.val < 319 then (121, 49) else (if i.val < 320 then (138, 224) else (40, 222))) else (if i.val < 322 then (118, 3) else (if i.val < 323 then (78, 89) else (129, 23)))))))))) else (if i.val < 486 then (if i.val < 405 then (if i.val < 364 then (if i.val < 344 then (if i.val < 334 then (if i.val < 329 then (if i.val < 326 then (if i.val < 325 then (83, 53) else (139, 175)) else (if i.val < 327 then (129, 162) else (if i.val < 328 then (14, 235) else (68, 100)))) else (if i.val < 331 then (if i.val < 330 then (131, 63) else (77, 43)) else (if i.val < 332 then (120, 219) else (if i.val < 333 then (34, 8) else (42, 210))))) else (if i.val < 339 then (if i.val < 336 then (if i.val < 335 then (117, 99) else (33, 62)) else (if i.val < 337 then (78, 185) else (if i.val < 338 then (41, 87) else (121, 161)))) else (if i.val < 341 then (if i.val < 340 then (53, 3) else (129, 99)) else (if i.val < 342 then (27, 168) else (if i.val < 343 then (135, 77) else (99, 183)))))) else (if i.val < 354 then (if i.val < 349 then (if i.val < 346 then (if i.val < 345 then (77, 61) else (122, 247)) else (if i.val < 347 then (27, 255) else (if i.val < 348 then (67, 137) else (141, 129)))) else (if i.val < 351 then (if i.val < 350 then (35, 126) else (129, 90)) else (if i.val < 352 then (44, 128) else (if i.val < 353 then (42, 249) else (113, 252))))) else (if i.val < 359 then (if i.val < 356 then (if i.val < 355 then (82, 193) else (123, 205)) else (if i.val < 357 then (105, 203) else (if i.val < 358 then (40, 146) else (120, 125)))) else (if i.val < 361 then (if i.val < 360 then (46, 91) else (47, 208)) else (if i.val < 362 then (4, 252) else (if i.val < 363 then (17, 96) else (61, 23))))))) else (if i.val < 384 then (if i.val < 374 then (if i.val < 369 then (if i.val < 366 then (if i.val < 365 then (92, 38) else (81, 214)) else (if i.val < 367 then (143, 99) else (if i.val < 368 then (135, 195) else (17, 157)))) else (if i.val < 371 then (if i.val < 370 then (124, 66) else (127, 223)) else (if i.val < 372 then (31, 205) else (if i.val < 373 then (22, 54) else (99, 131))))) else (if i.val < 379 then (if i.val < 376 then (if i.val < 375 then (135, 196) else (123, 103)) else (if i.val < 377 then (25, 71) else (if i.val < 378 then (133, 35) else (143, 221)))) else (if i.val < 381 then (if i.val < 380 then (127, 69) else (126, 192)) else (if i.val < 382 then (70, 4) else (if i.val < 383 then (127, 181) else (76, 215)))))) else (if i.val < 394 then (if i.val < 389 then (if i.val < 386 then (if i.val < 385 then (44, 236) else (73, 254)) else (if i.val < 387 then (39, 14) else (if i.val < 388 then (118, 138) else (18, 63)))) else (if i.val < 391 then (if i.val < 390 then (85, 216) else (33, 181)) else (if i.val < 392 then (92, 45) else (if i.val < 393 then (110, 186) else (103, 157))))) else (if i.val < 399 then (if i.val < 396 then (if i.val < 395 then (99, 25) else (99, 221)) else (if i.val < 397 then (47, 105) else (if i.val < 398 then (95, 17) else (83, 215)))) else (if i.val < 402 then (if i.val < 400 then (51, 45) else (if i.val < 401 then (96, 13) else (131, 182))) else (if i.val < 403 then (90, 177) else (if i.val < 404 then (123, 240) else (125, 49)))))))) else (if i.val < 445 then (if i.val < 425 then (if i.val < 415 then (if i.val < 410 then (if i.val < 407 then (if i.val < 406 then (41, 234) else (84, 45)) else (if i.val < 408 then (19, 196) else (if i.val < 409 then (142, 248) else (120, 167)))) else (if i.val < 412 then (if i.val < 411 then (70, 15) else (133, 151)) else (if i.val < 413 then (128, 141) else (if i.val < 414 then (122, 66) else (66, 85))))) else (if i.val < 420 then (if i.val < 417 then (if i.val < 416 then (38, 42) else (142, 202)) else (if i.val < 418 then (80, 76) else (if i.val < 419 then (23, 62) else (25, 13)))) else (if i.val < 422 then (if i.val < 421 then (0, 37) else (69, 214)) else (if i.val < 423 then (21, 209) else (if i.val < 424 then (35, 67) else (60, 48)))))) else (if i.val < 435 then (if i.val < 430 then (if i.val < 427 then (if i.val < 426 then (18, 219) else (78, 249)) else (if i.val < 428 then (138, 70) else (if i.val < 429 then (111, 16) else (103, 255)))) else (if i.val < 432 then (if i.val < 431 then (61, 4) else (58, 209)) else (if i.val < 433 then (133, 208) else (if i.val < 434 then (97, 197) else (5, 170))))) else (if i.val < 440 then (if i.val < 437 then (if i.val < 436 then (143, 28) else (7, 177)) else (if i.val < 438 then (72, 114) else (if i.val < 439 then (144, 49) else (140, 254)))) else (if i.val < 442 then (if i.val < 441 then (142, 117) else (74, 131)) else (if i.val < 443 then (89, 35) else (if i.val < 444 then (16, 177) else (135, 166))))))) else (if i.val < 465 then (if i.val < 455 then (if i.val < 450 then (if i.val < 447 then (if i.val < 446 then (127, 22) else (71, 58)) else (if i.val < 448 then (102, 193) else (if i.val < 449 then (110, 131) else (15, 23)))) else (if i.val < 452 then (if i.val < 451 then (142, 200) else (5, 83)) else (if i.val < 453 then (80, 186) else (if i.val < 454 then (134, 241) else (124, 207))))) else (if i.val < 460 then (if i.val < 457 then (if i.val < 456 then (17, 95) else (70, 36)) else (if i.val < 458 then (20, 206) else (if i.val < 459 then (126, 54) else (74, 172)))) else (if i.val < 462 then (if i.val < 461 then (43, 145) else (17, 142)) else (if i.val < 463 then (57, 22) else (if i.val < 464 then (119, 242) else (2, 9)))))) else (if i.val < 475 then (if i.val < 470 then (if i.val < 467 then (if i.val < 466 then (143, 225) else (33, 244)) else (if i.val < 468 then (49, 59) else (if i.val < 469 then (112, 171) else (0, 98)))) else (if i.val < 472 then (if i.val < 471 then (14, 247) else (59, 179)) else (if i.val < 473 then (32, 120) else (if i.val < 474 then (25, 150) else (28, 29))))) else (if i.val < 480 then (if i.val < 477 then (if i.val < 476 then (55, 213) else (46, 0)) else (if i.val < 478 then (25, 97) else (if i.val < 479 then (100, 243) else (43, 64)))) else (if i.val < 483 then (if i.val < 481 then (83, 223) else (if i.val < 482 then (56, 8) else (137, 171))) else (if i.val < 484 then (83, 251) else (if i.val < 485 then (31, 113) else (117, 72))))))))) else (if i.val < 567 then (if i.val < 526 then (if i.val < 506 then (if i.val < 496 then (if i.val < 491 then (if i.val < 488 then (if i.val < 487 then (1, 190) else (142, 192)) else (if i.val < 489 then (78, 73) else (if i.val < 490 then (17, 99) else (133, 228)))) else (if i.val < 493 then (if i.val < 492 then (38, 4) else (68, 206)) else (if i.val < 494 then (32, 139) else (if i.val < 495 then (40, 102) else (58, 224))))) else (if i.val < 501 then (if i.val < 498 then (if i.val < 497 then (50, 44) else (70, 192)) else (if i.val < 499 then (41, 94) else (if i.val < 500 then (88, 196) else (100, 251)))) else (if i.val < 503 then (if i.val < 502 then (5, 194) else (77, 79)) else (if i.val < 504 then (16, 64) else (if i.val < 505 then (22, 210) else (13, 90)))))) else (if i.val < 516 then (if i.val < 511 then (if i.val < 508 then (if i.val < 507 then (31, 106) else (33, 193)) else (if i.val < 509 then (139, 85) else (if i.val < 510 then (18, 251) else (142, 8)))) else (if i.val < 513 then (if i.val < 512 then (139, 186) else (50, 170)) else (if i.val < 514 then (41, 110) else (if i.val < 515 then (119, 205) else (77, 188))))) else (if i.val < 521 then (if i.val < 518 then (if i.val < 517 then (118, 232) else (55, 220)) else (if i.val < 519 then (56, 124) else (if i.val < 520 then (30, 140) else (19, 178)))) else (if i.val < 523 then (if i.val < 522 then (118, 160) else (138, 82)) else (if i.val < 524 then (107, 212) else (if i.val < 525 then (117, 213) else (10, 54))))))) else (if i.val < 546 then (if i.val < 536 then (if i.val < 531 then (if i.val < 528 then (if i.val < 527 then (112, 161) else (111, 236)) else (if i.val < 529 then (121, 240) else (if i.val < 530 then (26, 238) else (2, 130)))) else (if i.val < 533 then (if i.val < 532 then (143, 234) else (39, 229)) else (if i.val < 534 then (143, 229) else (if i.val < 535 then (99, 101) else (59, 170))))) else (if i.val < 541 then (if i.val < 538 then (if i.val < 537 then (82, 196) else (76, 43)) else (if i.val < 539 then (11, 6) else (if i.val < 540 then (67, 85) else (143, 228)))) else (if i.val < 543 then (if i.val < 542 then (88, 194) else (79, 84)) else (if i.val < 544 then (90, 247) else (if i.val < 545 then (89, 167) else (139, 204)))))) else (if i.val < 556 then (if i.val < 551 then (if i.val < 548 then (if i.val < 547 then (74, 203) else (123, 137)) else (if i.val < 549 then (96, 33) else (if i.val < 550 then (125, 245) else (139, 106)))) else (if i.val < 553 then (if i.val < 552 then (142, 115) else (125, 137)) else (if i.val < 554 then (136, 77) else (if i.val < 555 then (82, 247) else (100, 246))))) else (if i.val < 561 then (if i.val < 558 then (if i.val < 557 then (72, 236) else (118, 50)) else (if i.val < 559 then (96, 204) else (if i.val < 560 then (75, 174) else (83, 54)))) else (if i.val < 564 then (if i.val < 562 then (95, 201) else (if i.val < 563 then (135, 173) else (87, 48))) else (if i.val < 565 then (137, 145) else (if i.val < 566 then (116, 181) else (66, 132)))))))) else (if i.val < 607 then (if i.val < 587 then (if i.val < 577 then (if i.val < 572 then (if i.val < 569 then (if i.val < 568 then (131, 218) else (143, 67)) else (if i.val < 570 then (9, 211) else (if i.val < 571 then (93, 196) else (21, 87)))) else (if i.val < 574 then (if i.val < 573 then (128, 199) else (143, 146)) else (if i.val < 575 then (73, 170) else (if i.val < 576 then (131, 162) else (12, 131))))) else (if i.val < 582 then (if i.val < 579 then (if i.val < 578 then (81, 195) else (29, 157)) else (if i.val < 580 then (16, 11) else (if i.val < 581 then (54, 142) else (2, 82)))) else (if i.val < 584 then (if i.val < 583 then (10, 137) else (67, 84)) else (if i.val < 585 then (92, 168) else (if i.val < 586 then (97, 251) else (63, 160)))))) else (if i.val < 597 then (if i.val < 592 then (if i.val < 589 then (if i.val < 588 then (35, 149) else (89, 82)) else (if i.val < 590 then (38, 3) else (if i.val < 591 then (118, 71) else (18, 242)))) else (if i.val < 594 then (if i.val < 593 then (63, 224) else (3, 231)) else (if i.val < 595 then (45, 86) else (if i.val < 596 then (131, 41) else (20, 152))))) else (if i.val < 602 then (if i.val < 599 then (if i.val < 598 then (84, 190) else (67, 180)) else (if i.val < 600 then (34, 117) else (if i.val < 601 then (11, 29) else (124, 180)))) else (if i.val < 604 then (if i.val < 603 then (60, 168) else (29, 48)) else (if i.val < 605 then (71, 53) else (if i.val < 606 then (40, 94) else (124, 10))))))) else (if i.val < 627 then (if i.val < 617 then (if i.val < 612 then (if i.val < 609 then (if i.val < 608 then (27, 15) else (67, 100)) else (if i.val < 610 then (124, 14) else (if i.val < 611 then (27, 30) else (14, 187)))) else (if i.val < 614 then (if i.val < 613 then (61, 155) else (127, 29)) else (if i.val < 615 then (9, 203) else (if i.val < 616 then (45, 102) else (62, 21))))) else (if i.val < 622 then (if i.val < 619 then (if i.val < 618 then (56, 143) else (45, 143)) else (if i.val < 620 then (84, 16) else (if i.val < 621 then (59, 27) else (68, 170)))) else (if i.val < 624 then (if i.val < 623 then (11, 27) else (49, 225)) else (if i.val < 625 then (83, 231) else (if i.val < 626 then (5, 18) else (27, 128)))))) else (if i.val < 637 then (if i.val < 632 then (if i.val < 629 then (if i.val < 628 then (5, 4) else (31, 130)) else (if i.val < 630 then (1, 207) else (if i.val < 631 then (79, 158) else (2, 163)))) else (if i.val < 634 then (if i.val < 633 then (44, 127) else (26, 93)) else (if i.val < 635 then (14, 242) else (if i.val < 636 then (43, 182) else (99, 20))))) else (if i.val < 642 then (if i.val < 639 then (if i.val < 638 then (47, 119) else (14, 184)) else (if i.val < 640 then (42, 179) else (if i.val < 641 then (42, 187) else (74, 126)))) else (if i.val < 645 then (if i.val < 643 then (98, 163) else (if i.val < 644 then (14, 212) else (56, 132))) else (if i.val < 646 then (10, 9) else (if i.val < 647 then (14, 213) else (50, 240)))))))))))

def g32p_supplierGroup06_classify : Fin 648 → Fin 102 :=
  fun i => (if i.val < 324 then (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 0 else 34) else (if i.val < 3 then 32 else (if i.val < 4 then 69 else 45))) else (if i.val < 7 then (if i.val < 6 then 97 else 46) else (if i.val < 8 then 34 else (if i.val < 9 then 69 else 46)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 45 else 34) else (if i.val < 13 then 95 else (if i.val < 14 then 34 else 34))) else (if i.val < 17 then (if i.val < 16 then 99 else 46) else (if i.val < 18 then 69 else (if i.val < 19 then 46 else 35))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then 69 else 6) else (if i.val < 23 then 13 else (if i.val < 24 then 32 else 6))) else (if i.val < 27 then (if i.val < 26 then 21 else 46) else (if i.val < 28 then 30 else (if i.val < 29 then 13 else 46)))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then 34 else 21) else (if i.val < 33 then 32 else (if i.val < 34 then 21 else 13))) else (if i.val < 37 then (if i.val < 36 then 21 else 46) else (if i.val < 38 then 30 else (if i.val < 39 then 21 else 13)))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then 35 else 46) else (if i.val < 43 then 35 else (if i.val < 44 then 21 else 30))) else (if i.val < 47 then (if i.val < 46 then 21 else 84) else (if i.val < 48 then 46 else (if i.val < 49 then 21 else 46)))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then 13 else 35) else (if i.val < 53 then 21 else (if i.val < 54 then 69 else 84))) else (if i.val < 57 then (if i.val < 56 then 21 else 84) else (if i.val < 58 then 30 else (if i.val < 59 then 30 else 21))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then 13 else 21) else (if i.val < 63 then 21 else (if i.val < 64 then 30 else 13))) else (if i.val < 67 then (if i.val < 66 then 30 else 101) else (if i.val < 68 then 30 else (if i.val < 69 then 69 else 13)))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then 30 else 32) else (if i.val < 73 then 69 else (if i.val < 74 then 100 else 69))) else (if i.val < 78 then (if i.val < 76 then 69 else (if i.val < 77 then 96 else 30)) else (if i.val < 79 then 13 else (if i.val < 80 then 30 else 75))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then 92 else 69) else (if i.val < 84 then 45 else (if i.val < 85 then 32 else 21))) else (if i.val < 88 then (if i.val < 87 then 46 else 69) else (if i.val < 89 then 46 else (if i.val < 90 then 34 else 100)))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then 30 else 21) else (if i.val < 94 then 69 else (if i.val < 95 then 30 else 69))) else (if i.val < 98 then (if i.val < 97 then 21 else 46) else (if i.val < 99 then 30 else (if i.val < 100 then 69 else 69))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then 46 else 45) else (if i.val < 104 then 30 else (if i.val < 105 then 34 else 13))) else (if i.val < 108 then (if i.val < 107 then 75 else 46) else (if i.val < 109 then 34 else (if i.val < 110 then 69 else 46)))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then 69 else 21) else (if i.val < 114 then 46 else (if i.val < 115 then 30 else 21))) else (if i.val < 118 then (if i.val < 117 then 34 else 21) else (if i.val < 119 then 46 else (if i.val < 120 then 21 else 84)))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then 30 else 46) else (if i.val < 124 then 30 else (if i.val < 125 then 76 else 21))) else (if i.val < 128 then (if i.val < 127 then 30 else 34) else (if i.val < 129 then 67 else (if i.val < 130 then 34 else 6)))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then 46 else 46) else (if i.val < 134 then 30 else (if i.val < 135 then 21 else 30))) else (if i.val < 138 then (if i.val < 137 then 30 else 46) else (if i.val < 139 then 21 else (if i.val < 140 then 46 else 69))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then 21 else 46) else (if i.val < 144 then 30 else (if i.val < 145 then 30 else 69))) else (if i.val < 148 then (if i.val < 147 then 46 else 69) else (if i.val < 149 then 46 else (if i.val < 150 then 34 else 21)))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then 84 else 30) else (if i.val < 154 then 46 else (if i.val < 155 then 34 else 6))) else (if i.val < 159 then (if i.val < 157 then 30 else (if i.val < 158 then 67 else 46)) else (if i.val < 160 then 46 else (if i.val < 161 then 69 else 46)))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then 34 else 69) else (if i.val < 165 then 13 else (if i.val < 166 then 69 else 92))) else (if i.val < 169 then (if i.val < 168 then 46 else 32) else (if i.val < 170 then 46 else (if i.val < 171 then 34 else 21)))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then 30 else 46) else (if i.val < 175 then 13 else (if i.val < 176 then 34 else 30))) else (if i.val < 179 then (if i.val < 178 then 46 else 30) else (if i.val < 180 then 46 else (if i.val < 181 then 13 else 69))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then 21 else 46) else (if i.val < 185 then 34 else (if i.val < 186 then 46 else 46))) else (if i.val < 189 then (if i.val < 188 then 69 else 34) else (if i.val < 190 then 6 else (if i.val < 191 then 84 else 30)))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then 21 else 34) else (if i.val < 195 then 30 else (if i.val < 196 then 69 else 6))) else (if i.val < 199 then (if i.val < 198 then 34 else 46) else (if i.val < 200 then 30 else (if i.val < 201 then 21 else 75)))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then 30 else 75) else (if i.val < 205 then 46 else (if i.val < 206 then 21 else 46))) else (if i.val < 209 then (if i.val < 208 then 35 else 30) else (if i.val < 210 then 46 else (if i.val < 211 then 30 else 75)))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then 46 else 35) else (if i.val < 215 then 35 else (if i.val < 216 then 21 else 21))) else (if i.val < 219 then (if i.val < 218 then 46 else 46) else (if i.val < 220 then 21 else (if i.val < 221 then 34 else 21))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then 11 else 34) else (if i.val < 225 then 95 else (if i.val < 226 then 30 else 34))) else (if i.val < 229 then (if i.val < 228 then 75 else 46) else (if i.val < 230 then 2 else (if i.val < 231 then 11 else 34)))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then 44 else 34) else (if i.val < 235 then 21 else (if i.val < 236 then 46 else 75))) else (if i.val < 240 then (if i.val < 238 then 13 else (if i.val < 239 then 30 else 34)) else (if i.val < 241 then 46 else (if i.val < 242 then 46 else 30))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then 30 else 21) else (if i.val < 246 then 95 else (if i.val < 247 then 46 else 35))) else (if i.val < 250 then (if i.val < 249 then 21 else 35) else (if i.val < 251 then 69 else (if i.val < 252 then 30 else 6)))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then 46 else 32) else (if i.val < 256 then 21 else (if i.val < 257 then 34 else 6))) else (if i.val < 260 then (if i.val < 259 then 46 else 34) else (if i.val < 261 then 13 else (if i.val < 262 then 75 else 30))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then 30 else 69) else (if i.val < 266 then 21 else (if i.val < 267 then 35 else 13))) else (if i.val < 270 then (if i.val < 269 then 21 else 13) else (if i.val < 271 then 44 else (if i.val < 272 then 46 else 46)))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then 69 else 46) else (if i.val < 276 then 21 else (if i.val < 277 then 21 else 30))) else (if i.val < 280 then (if i.val < 279 then 2 else 21) else (if i.val < 281 then 84 else (if i.val < 282 then 21 else 21)))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then 30 else 30) else (if i.val < 286 then 34 else (if i.val < 287 then 21 else 46))) else (if i.val < 290 then (if i.val < 289 then 30 else 46) else (if i.val < 291 then 34 else (if i.val < 292 then 34 else 69)))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then 13 else 30) else (if i.val < 296 then 46 else (if i.val < 297 then 30 else 69))) else (if i.val < 300 then (if i.val < 299 then 34 else 21) else (if i.val < 301 then 30 else (if i.val < 302 then 34 else 13))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then 13 else 32) else (if i.val < 306 then 46 else (if i.val < 307 then 93 else 21))) else (if i.val < 310 then (if i.val < 309 then 13 else 30) else (if i.val < 311 then 13 else (if i.val < 312 then 46 else 21)))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then 30 else 21) else (if i.val < 316 then 34 else (if i.val < 317 then 34 else 69))) else (if i.val < 321 then (if i.val < 319 then 46 else (if i.val < 320 then 30 else 69)) else (if i.val < 322 then 21 else (if i.val < 323 then 30 else 21))))))))) else (if i.val < 486 then (if i.val < 405 then (if i.val < 364 then (if i.val < 344 then (if i.val < 334 then (if i.val < 329 then (if i.val < 326 then (if i.val < 325 then 21 else 30) else (if i.val < 327 then 21 else (if i.val < 328 then 1 else 69))) else (if i.val < 331 then (if i.val < 330 then 46 else 30) else (if i.val < 332 then 46 else (if i.val < 333 then 13 else 69)))) else (if i.val < 339 then (if i.val < 336 then (if i.val < 335 then 21 else 21) else (if i.val < 337 then 34 else (if i.val < 338 then 69 else 46))) else (if i.val < 341 then (if i.val < 340 then 69 else 21) else (if i.val < 342 then 34 else (if i.val < 343 then 21 else 13))))) else (if i.val < 354 then (if i.val < 349 then (if i.val < 346 then (if i.val < 345 then 30 else 46) else (if i.val < 347 then 30 else (if i.val < 348 then 69 else 46))) else (if i.val < 351 then (if i.val < 350 then 13 else 21) else (if i.val < 352 then 13 else (if i.val < 353 then 21 else 46)))) else (if i.val < 359 then (if i.val < 356 then (if i.val < 355 then 69 else 46) else (if i.val < 357 then 30 else (if i.val < 358 then 21 else 21))) else (if i.val < 361 then (if i.val < 360 then 46 else 13) else (if i.val < 362 then 93 else (if i.val < 363 then 13 else 32)))))) else (if i.val < 384 then (if i.val < 374 then (if i.val < 369 then (if i.val < 366 then (if i.val < 365 then 21 else 69) else (if i.val < 367 then 21 else (if i.val < 368 then 21 else 1))) else (if i.val < 371 then (if i.val < 370 then 46 else 30) else (if i.val < 372 then 100 else (if i.val < 373 then 69 else 45)))) else (if i.val < 379 then (if i.val < 376 then (if i.val < 375 then 21 else 45) else (if i.val < 377 then 13 else (if i.val < 378 then 30 else 46))) else (if i.val < 381 then (if i.val < 380 then 30 else 30) else (if i.val < 382 then 13 else (if i.val < 383 then 30 else 30))))) else (if i.val < 394 then (if i.val < 389 then (if i.val < 386 then (if i.val < 385 then 13 else 13) else (if i.val < 387 then 24 else (if i.val < 388 then 21 else 13))) else (if i.val < 391 then (if i.val < 390 then 30 else 13) else (if i.val < 392 then 24 else (if i.val < 393 then 46 else 30)))) else (if i.val < 399 then (if i.val < 396 then (if i.val < 395 then 46 else 46) else (if i.val < 397 then 13 else (if i.val < 398 then 69 else 13))) else (if i.val < 402 then (if i.val < 400 then 34 else (if i.val < 401 then 21 else 30)) else (if i.val < 403 then 30 else (if i.val < 404 then 46 else 30))))))) else (if i.val < 445 then (if i.val < 425 then (if i.val < 415 then (if i.val < 410 then (if i.val < 407 then (if i.val < 406 then 69 else 13) else (if i.val < 408 then 34 else (if i.val < 409 then 21 else 21))) else (if i.val < 412 then (if i.val < 411 then 13 else 30) else (if i.val < 413 then 21 else (if i.val < 414 then 46 else 69)))) else (if i.val < 420 then (if i.val < 417 then (if i.val < 416 then 34 else 30) else (if i.val < 418 then 34 else (if i.val < 419 then 21 else 46))) else (if i.val < 422 then (if i.val < 421 then 37 else 45) else (if i.val < 423 then 78 else (if i.val < 424 then 13 else 13))))) else (if i.val < 435 then (if i.val < 430 then (if i.val < 427 then (if i.val < 426 then 30 else 93) else (if i.val < 428 then 46 else (if i.val < 429 then 13 else 30))) else (if i.val < 432 then (if i.val < 431 then 32 else 13) else (if i.val < 433 then 30 else (if i.val < 434 then 46 else 98)))) else (if i.val < 440 then (if i.val < 437 then (if i.val < 436 then 21 else 28) else (if i.val < 438 then 84 else (if i.val < 439 then 30 else 21))) else (if i.val < 442 then (if i.val < 441 then 30 else 46) else (if i.val < 443 then 30 else (if i.val < 444 then 13 else 21)))))) else (if i.val < 465 then (if i.val < 455 then (if i.val < 450 then (if i.val < 447 then (if i.val < 446 then 30 else 13) else (if i.val < 448 then 30 else (if i.val < 449 then 84 else 28))) else (if i.val < 452 then (if i.val < 451 then 30 else 78) else (if i.val < 453 then 6 else (if i.val < 454 then 21 else 30)))) else (if i.val < 460 then (if i.val < 457 then (if i.val < 456 then 13 else 46) else (if i.val < 458 then 30 else (if i.val < 459 then 30 else 13))) else (if i.val < 462 then (if i.val < 461 then 13 else 13) else (if i.val < 463 then 4 else (if i.val < 464 then 21 else 28))))) else (if i.val < 475 then (if i.val < 470 then (if i.val < 467 then (if i.val < 466 then 46 else 13) else (if i.val < 468 then 4 else (if i.val < 469 then 21 else 98))) else (if i.val < 472 then (if i.val < 471 then 24 else 13) else (if i.val < 473 then 4 else (if i.val < 474 then 13 else 35)))) else (if i.val < 480 then (if i.val < 477 then (if i.val < 476 then 84 else 13) else (if i.val < 478 then 46 else (if i.val < 479 then 46 else 21))) else (if i.val < 483 then (if i.val < 481 then 84 else (if i.val < 482 then 98 else 46)) else (if i.val < 484 then 13 else (if i.val < 485 then 92 else 21)))))))) else (if i.val < 567 then (if i.val < 526 then (if i.val < 506 then (if i.val < 496 then (if i.val < 491 then (if i.val < 488 then (if i.val < 487 then 1 else 30) else (if i.val < 489 then 34 else (if i.val < 490 then 28 else 30))) else (if i.val < 493 then (if i.val < 492 then 30 else 21) else (if i.val < 494 then 4 else (if i.val < 495 then 21 else 56)))) else (if i.val < 501 then (if i.val < 498 then (if i.val < 497 then 30 else 13) else (if i.val < 499 then 67 else (if i.val < 500 then 30 else 45))) else (if i.val < 503 then (if i.val < 502 then 100 else 30) else (if i.val < 504 then 24 else (if i.val < 505 then 75 else 92))))) else (if i.val < 516 then (if i.val < 511 then (if i.val < 508 then (if i.val < 507 then 92 else 1) else (if i.val < 509 then 30 else (if i.val < 510 then 32 else 21))) else (if i.val < 513 then (if i.val < 512 then 30 else 4) else (if i.val < 514 then 21 else (if i.val < 515 then 21 else 30)))) else (if i.val < 521 then (if i.val < 518 then (if i.val < 517 then 21 else 98) else (if i.val < 519 then 78 else (if i.val < 520 then 78 else 30))) else (if i.val < 523 then (if i.val < 522 then 75 else 46) else (if i.val < 524 then 6 else (if i.val < 525 then 21 else 21)))))) else (if i.val < 546 then (if i.val < 536 then (if i.val < 531 then (if i.val < 528 then (if i.val < 527 then 21 else 78) else (if i.val < 529 then 46 else (if i.val < 530 then 30 else 24))) else (if i.val < 533 then (if i.val < 532 then 46 else 6) else (if i.val < 534 then 46 else (if i.val < 535 then 46 else 46)))) else (if i.val < 541 then (if i.val < 538 then (if i.val < 537 then 69 else 34) else (if i.val < 539 then 69 else (if i.val < 540 then 21 else 46))) else (if i.val < 543 then (if i.val < 542 then 30 else 34) else (if i.val < 544 then 30 else (if i.val < 545 then 30 else 30))))) else (if i.val < 556 then (if i.val < 551 then (if i.val < 548 then (if i.val < 547 then 46 else 46) else (if i.val < 549 then 21 else (if i.val < 550 then 30 else 30))) else (if i.val < 553 then (if i.val < 552 then 30 else 30) else (if i.val < 554 then 21 else (if i.val < 555 then 75 else 46)))) else (if i.val < 561 then (if i.val < 558 then (if i.val < 557 then 46 else 21) else (if i.val < 559 then 21 else (if i.val < 560 then 4 else 69))) else (if i.val < 564 then (if i.val < 562 then 21 else (if i.val < 563 then 21 else 46)) else (if i.val < 565 then 46 else (if i.val < 566 then 30 else 21))))))) else (if i.val < 607 then (if i.val < 587 then (if i.val < 577 then (if i.val < 572 then (if i.val < 569 then (if i.val < 568 then 30 else 21) else (if i.val < 570 then 21 else (if i.val < 571 then 21 else 21))) else (if i.val < 574 then (if i.val < 573 then 21 else 46) else (if i.val < 575 then 46 else (if i.val < 576 then 21 else 45)))) else (if i.val < 582 then (if i.val < 579 then (if i.val < 578 then 75 else 95) else (if i.val < 580 then 44 else (if i.val < 581 then 21 else 34))) else (if i.val < 584 then (if i.val < 583 then 69 else 21) else (if i.val < 585 then 21 else (if i.val < 586 then 46 else 34))))) else (if i.val < 597 then (if i.val < 592 then (if i.val < 589 then (if i.val < 588 then 34 else 34) else (if i.val < 590 then 34 else (if i.val < 591 then 21 else 34))) else (if i.val < 594 then (if i.val < 593 then 34 else 34) else (if i.val < 595 then 56 else (if i.val < 596 then 46 else 34)))) else (if i.val < 602 then (if i.val < 599 then (if i.val < 598 then 46 else 21) else (if i.val < 600 then 46 else (if i.val < 601 then 69 else 45))) else (if i.val < 604 then (if i.val < 603 then 30 else 69) else (if i.val < 605 then 45 else (if i.val < 606 then 69 else 46)))))) else (if i.val < 627 then (if i.val < 617 then (if i.val < 612 then (if i.val < 609 then (if i.val < 608 then 88 else 69) else (if i.val < 610 then 46 else (if i.val < 611 then 88 else 93))) else (if i.val < 614 then (if i.val < 613 then 32 else 30) else (if i.val < 615 then 30 else (if i.val < 616 then 56 else 30)))) else (if i.val < 622 then (if i.val < 619 then (if i.val < 618 then 76 else 56) else (if i.val < 620 then 56 else (if i.val < 621 then 11 else 6))) else (if i.val < 624 then (if i.val < 623 then 67 else 88) else (if i.val < 625 then 11 else (if i.val < 626 then 87 else 87))))) else (if i.val < 637 then (if i.val < 632 then (if i.val < 629 then (if i.val < 628 then 88 else 87) else (if i.val < 630 then 2 else (if i.val < 631 then 35 else 44))) else (if i.val < 634 then (if i.val < 633 then 11 else 45) else (if i.val < 635 then 2 else (if i.val < 636 then 56 else 84)))) else (if i.val < 642 then (if i.val < 639 then (if i.val < 638 then 11 else 87) else (if i.val < 640 then 69 else (if i.val < 641 then 69 else 46))) else (if i.val < 645 then (if i.val < 643 then 46 else (if i.val < 644 then 76 else 76)) else (if i.val < 646 then 24 else (if i.val < 647 then 78 else 92))))))))))

def g32p_supplierGroup06_support : Finset (Fin 102) :=
  {0, 1, 2, 4, 6, 11, 13, 21, 24, 28, 30, 32, 34, 35, 37, 44, 45, 46, 56, 67, 69, 75, 76, 78, 84, 87, 88, 92, 93, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup06_matrix_000 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 0 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 0 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 0 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 0 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 0 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_001 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 1 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 1 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 1 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 1 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 1 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_002 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 2 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 2 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 2 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 2 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 2 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_003 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 3 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 3 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 3 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 3 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 3 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_004 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 4 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 4 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 4 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 4 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 4 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_005 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 5 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 5 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 5 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 5 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 5 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_006 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 6 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 6 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 6 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 6 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 6 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_007 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 7 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 7 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 7 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 7 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 7 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_008 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 8 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 8 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 8 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 8 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 8 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_009 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 9 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 9 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 9 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 9 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 9 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_010 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 10 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 10 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 10 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 10 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 10 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_011 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 11 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 11 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 11 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 11 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 11 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_012 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 12 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 12 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 12 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 12 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 12 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_013 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 13 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 13 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 13 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 13 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 13 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_014 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 14 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 14 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 14 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 14 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 14 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_015 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 15 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 15 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 15 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 15 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 15 r) ∈ g32p_supplierGroup06_support := by
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

theorem g32p_supplierGroup06_matrix_016 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 16 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 16 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 16 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 16 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 16 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_017 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 17 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 17 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 17 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 17 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 17 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_018 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 18 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 18 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 18 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 18 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 18 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_019 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 19 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 19 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 19 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 19 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 19 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_020 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 20 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 20 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 20 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 20 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 20 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_021 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 21 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 21 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 21 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 21 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 21 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_022 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 22 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 22 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 22 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 22 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 22 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_023 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 23 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 23 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 23 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 23 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 23 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_024 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 24 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 24 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 24 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 24 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 24 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_025 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 25 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 25 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 25 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 25 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 25 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_026 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 26 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 26 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 26 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 26 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 26 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_027 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 27 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 27 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 27 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_027 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 27 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 27 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 27 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_027 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 27 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_028 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 28 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 28 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 28 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_028 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 28 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 28 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 28 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_028 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 28 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_029 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 29 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 29 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 29 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_029 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 29 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 29 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 29 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_029 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 29 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_030 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 30 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 30 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 30 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_030 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 30 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 30 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 30 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_030 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 30 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_031 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 31 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 31 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 31 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_031 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 31 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 31 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 31 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_031 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 31 r) ∈ g32p_supplierGroup06_support := by
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

theorem g32p_supplierGroup06_matrix_032 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 32 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 32 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 32 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_032 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 32 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 32 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 32 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_032 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 32 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_033 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 33 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 33 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 33 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_033 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 33 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 33 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 33 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_033 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 33 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_034 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 34 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 34 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 34 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_034 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 34 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 34 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 34 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_034 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 34 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_035 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 35 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 35 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 35 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_035 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 35 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 35 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 35 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_035 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 35 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_036 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 36 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 36 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 36 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_036 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 36 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 36 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 36 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_036 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 36 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_037 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 37 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 37 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 37 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_037 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 37 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 37 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 37 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_037 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 37 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_038 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 38 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 38 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 38 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_038 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 38 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 38 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 38 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_038 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 38 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_039 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 39 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 39 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 39 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_039 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 39 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 39 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 39 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_039 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 39 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

theorem g32p_supplierGroup06_matrix_040 : ∀ r : Fin 16,
    g32p_row08_groupNodes (g32p_finBlockIndex 648 40 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 40 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 40 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup06_class_040 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup06_source (g32p_finBlockIndex 648 40 r)).1 (g32p_supplierGroup06_source (g32p_finBlockIndex 648 40 r)).2 =
      g32p_supplierGroup06_classify (g32p_finBlockIndex 648 40 r) := by
  decide +kernel

theorem g32p_supplierGroup06_support_040 : ∀ r : Fin 16,
    g32p_supplierGroup06_classify (g32p_finBlockIndex 648 40 r) ∈ g32p_supplierGroup06_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
