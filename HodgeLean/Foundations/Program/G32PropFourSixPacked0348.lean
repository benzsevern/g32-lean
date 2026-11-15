import HodgeLean.Foundations.Program.G32PropFourSixPacked0347
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_002 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 2 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_002_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 0 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 0 15 15, g32p_row07_traceSegment_002_0000_0015, g32p_row07_traceSegment_002_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 30 15 15, g32p_row07_traceSegment_002_0030_0015, g32p_row07_traceSegment_002_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_002 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 0 30 30, g32p_row07_traceSegment_002_0000_0030, g32p_row07_traceSegment_002_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 60 15 15, g32p_row07_traceSegment_002_0060_0015, g32p_row07_traceSegment_002_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 90 15 16, g32p_row07_traceSegment_002_0090_0015, g32p_row07_traceSegment_002_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 60 30 31, g32p_row07_traceSegment_002_0060_0030, g32p_row07_traceSegment_002_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_002 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 0 60 61, g32p_row07_traceSegment_002_0000_0060, g32p_row07_traceSegment_002_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 121 15 15, g32p_row07_traceSegment_002_0121_0015, g32p_row07_traceSegment_002_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 151 15 16, g32p_row07_traceSegment_002_0151_0015, g32p_row07_traceSegment_002_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 121 30 31, g32p_row07_traceSegment_002_0121_0030, g32p_row07_traceSegment_002_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 182 15 15, g32p_row07_traceSegment_002_0182_0015, g32p_row07_traceSegment_002_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 212 15 16, g32p_row07_traceSegment_002_0212_0015, g32p_row07_traceSegment_002_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 182 30 31, g32p_row07_traceSegment_002_0182_0030, g32p_row07_traceSegment_002_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_002 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 121 61 61, g32p_row07_traceSegment_002_0121_0061, g32p_row07_traceSegment_002_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_002 0 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 0 121 122, g32p_row07_traceSegment_002_0000_0121, g32p_row07_traceSegment_002_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 243 15 15, g32p_row07_traceSegment_002_0243_0015, g32p_row07_traceSegment_002_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 273 15 15, g32p_row07_traceSegment_002_0273_0015, g32p_row07_traceSegment_002_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_002 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 243 30 30, g32p_row07_traceSegment_002_0243_0030, g32p_row07_traceSegment_002_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 303 15 15, g32p_row07_traceSegment_002_0303_0015, g32p_row07_traceSegment_002_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 333 15 16, g32p_row07_traceSegment_002_0333_0015, g32p_row07_traceSegment_002_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 303 30 31, g32p_row07_traceSegment_002_0303_0030, g32p_row07_traceSegment_002_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_002 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 243 60 61, g32p_row07_traceSegment_002_0243_0060, g32p_row07_traceSegment_002_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 364 15 15, g32p_row07_traceSegment_002_0364_0015, g32p_row07_traceSegment_002_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 394 15 16, g32p_row07_traceSegment_002_0394_0015, g32p_row07_traceSegment_002_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 364 30 31, g32p_row07_traceSegment_002_0364_0030, g32p_row07_traceSegment_002_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 425 15 15, g32p_row07_traceSegment_002_0425_0015, g32p_row07_traceSegment_002_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 455 15 16, g32p_row07_traceSegment_002_0455_0015, g32p_row07_traceSegment_002_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 425 30 31, g32p_row07_traceSegment_002_0425_0030, g32p_row07_traceSegment_002_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_002 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 364 61 61, g32p_row07_traceSegment_002_0364_0061, g32p_row07_traceSegment_002_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_002 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 243 121 122, g32p_row07_traceSegment_002_0243_0121, g32p_row07_traceSegment_002_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_002 0 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 0 243 243, g32p_row07_traceSegment_002_0000_0243, g32p_row07_traceSegment_002_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 486 15 15, g32p_row07_traceSegment_002_0486_0015, g32p_row07_traceSegment_002_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 516 15 15, g32p_row07_traceSegment_002_0516_0015, g32p_row07_traceSegment_002_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_002 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 486 30 30, g32p_row07_traceSegment_002_0486_0030, g32p_row07_traceSegment_002_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 546 15 15, g32p_row07_traceSegment_002_0546_0015, g32p_row07_traceSegment_002_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 576 15 16, g32p_row07_traceSegment_002_0576_0015, g32p_row07_traceSegment_002_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 546 30 31, g32p_row07_traceSegment_002_0546_0030, g32p_row07_traceSegment_002_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_002 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 486 60 61, g32p_row07_traceSegment_002_0486_0060, g32p_row07_traceSegment_002_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 607 15 15, g32p_row07_traceSegment_002_0607_0015, g32p_row07_traceSegment_002_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 637 15 16, g32p_row07_traceSegment_002_0637_0015, g32p_row07_traceSegment_002_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 607 30 31, g32p_row07_traceSegment_002_0607_0030, g32p_row07_traceSegment_002_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 668 15 15, g32p_row07_traceSegment_002_0668_0015, g32p_row07_traceSegment_002_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 698 15 16, g32p_row07_traceSegment_002_0698_0015, g32p_row07_traceSegment_002_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 668 30 31, g32p_row07_traceSegment_002_0668_0030, g32p_row07_traceSegment_002_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_002 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 607 61 61, g32p_row07_traceSegment_002_0607_0061, g32p_row07_traceSegment_002_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_002 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 486 121 122, g32p_row07_traceSegment_002_0486_0121, g32p_row07_traceSegment_002_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 729 15 15, g32p_row07_traceSegment_002_0729_0015, g32p_row07_traceSegment_002_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 759 15 15, g32p_row07_traceSegment_002_0759_0015, g32p_row07_traceSegment_002_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_002 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 729 30 30, g32p_row07_traceSegment_002_0729_0030, g32p_row07_traceSegment_002_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 789 15 15, g32p_row07_traceSegment_002_0789_0015, g32p_row07_traceSegment_002_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 819 15 16, g32p_row07_traceSegment_002_0819_0015, g32p_row07_traceSegment_002_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 789 30 31, g32p_row07_traceSegment_002_0789_0030, g32p_row07_traceSegment_002_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_002 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 729 60 61, g32p_row07_traceSegment_002_0729_0060, g32p_row07_traceSegment_002_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 850 15 15, g32p_row07_traceSegment_002_0850_0015, g32p_row07_traceSegment_002_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 880 15 16, g32p_row07_traceSegment_002_0880_0015, g32p_row07_traceSegment_002_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 850 30 31, g32p_row07_traceSegment_002_0850_0030, g32p_row07_traceSegment_002_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 911 15 15, g32p_row07_traceSegment_002_0911_0015, g32p_row07_traceSegment_002_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 941 15 16, g32p_row07_traceSegment_002_0941_0015, g32p_row07_traceSegment_002_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 911 30 31, g32p_row07_traceSegment_002_0911_0030, g32p_row07_traceSegment_002_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_002 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 850 61 61, g32p_row07_traceSegment_002_0850_0061, g32p_row07_traceSegment_002_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_002 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 729 121 122, g32p_row07_traceSegment_002_0729_0121, g32p_row07_traceSegment_002_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_002 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 486 243 243, g32p_row07_traceSegment_002_0486_0243, g32p_row07_traceSegment_002_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_002 0 972 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 0 486 486, g32p_row07_traceSegment_002_0000_0486, g32p_row07_traceSegment_002_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 972 15 15, g32p_row07_traceSegment_002_0972_0015, g32p_row07_traceSegment_002_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1002 15 15, g32p_row07_traceSegment_002_1002_0015, g32p_row07_traceSegment_002_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_002 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 972 30 30, g32p_row07_traceSegment_002_0972_0030, g32p_row07_traceSegment_002_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1032 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1032 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1032 15 15, g32p_row07_traceSegment_002_1032_0015, g32p_row07_traceSegment_002_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1062 15 16, g32p_row07_traceSegment_002_1062_0015, g32p_row07_traceSegment_002_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1032 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1032 30 31, g32p_row07_traceSegment_002_1032_0030, g32p_row07_traceSegment_002_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_002 972 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 972 60 61, g32p_row07_traceSegment_002_0972_0060, g32p_row07_traceSegment_002_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1093 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1093 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1093 15 15, g32p_row07_traceSegment_002_1093_0015, g32p_row07_traceSegment_002_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1123 15 16, g32p_row07_traceSegment_002_1123_0015, g32p_row07_traceSegment_002_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1093 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1093 30 31, g32p_row07_traceSegment_002_1093_0030, g32p_row07_traceSegment_002_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1169 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1154 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1154 15 15, g32p_row07_traceSegment_002_1154_0015, g32p_row07_traceSegment_002_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1184 15 16, g32p_row07_traceSegment_002_1184_0015, g32p_row07_traceSegment_002_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1154 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1154 30 31, g32p_row07_traceSegment_002_1154_0030, g32p_row07_traceSegment_002_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_002 1093 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1093 61 61, g32p_row07_traceSegment_002_1093_0061, g32p_row07_traceSegment_002_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_002 972 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 972 121 122, g32p_row07_traceSegment_002_0972_0121, g32p_row07_traceSegment_002_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1215 15 15, g32p_row07_traceSegment_002_1215_0015, g32p_row07_traceSegment_002_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1245 15 15, g32p_row07_traceSegment_002_1245_0015, g32p_row07_traceSegment_002_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_002 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1215 30 30, g32p_row07_traceSegment_002_1215_0030, g32p_row07_traceSegment_002_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1275 15 15, g32p_row07_traceSegment_002_1275_0015, g32p_row07_traceSegment_002_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1305 15 16, g32p_row07_traceSegment_002_1305_0015, g32p_row07_traceSegment_002_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1275 30 31, g32p_row07_traceSegment_002_1275_0030, g32p_row07_traceSegment_002_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_002 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1215 60 61, g32p_row07_traceSegment_002_1215_0060, g32p_row07_traceSegment_002_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1336 15 15, g32p_row07_traceSegment_002_1336_0015, g32p_row07_traceSegment_002_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1366 15 16, g32p_row07_traceSegment_002_1366_0015, g32p_row07_traceSegment_002_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1336 30 31, g32p_row07_traceSegment_002_1336_0030, g32p_row07_traceSegment_002_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1397 15 15, g32p_row07_traceSegment_002_1397_0015, g32p_row07_traceSegment_002_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1427 15 16, g32p_row07_traceSegment_002_1427_0015, g32p_row07_traceSegment_002_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1397 30 31, g32p_row07_traceSegment_002_1397_0030, g32p_row07_traceSegment_002_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_002 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1336 61 61, g32p_row07_traceSegment_002_1336_0061, g32p_row07_traceSegment_002_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_002 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1215 121 122, g32p_row07_traceSegment_002_1215_0121, g32p_row07_traceSegment_002_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_002 972 486 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 972 243 243, g32p_row07_traceSegment_002_0972_0243, g32p_row07_traceSegment_002_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1458 15 15, g32p_row07_traceSegment_002_1458_0015, g32p_row07_traceSegment_002_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1488 15 15, g32p_row07_traceSegment_002_1488_0015, g32p_row07_traceSegment_002_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_002 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1458 30 30, g32p_row07_traceSegment_002_1458_0030, g32p_row07_traceSegment_002_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1518 15 15, g32p_row07_traceSegment_002_1518_0015, g32p_row07_traceSegment_002_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1548 15 16, g32p_row07_traceSegment_002_1548_0015, g32p_row07_traceSegment_002_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1518 30 31, g32p_row07_traceSegment_002_1518_0030, g32p_row07_traceSegment_002_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_002 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1458 60 61, g32p_row07_traceSegment_002_1458_0060, g32p_row07_traceSegment_002_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1579 15 15, g32p_row07_traceSegment_002_1579_0015, g32p_row07_traceSegment_002_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1609 15 16, g32p_row07_traceSegment_002_1609_0015, g32p_row07_traceSegment_002_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1579 30 31, g32p_row07_traceSegment_002_1579_0030, g32p_row07_traceSegment_002_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1640 15 15, g32p_row07_traceSegment_002_1640_0015, g32p_row07_traceSegment_002_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1670 15 16, g32p_row07_traceSegment_002_1670_0015, g32p_row07_traceSegment_002_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1640 30 31, g32p_row07_traceSegment_002_1640_0030, g32p_row07_traceSegment_002_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_002 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1579 61 61, g32p_row07_traceSegment_002_1579_0061, g32p_row07_traceSegment_002_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_002 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1458 121 122, g32p_row07_traceSegment_002_1458_0121, g32p_row07_traceSegment_002_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1701 15 15, g32p_row07_traceSegment_002_1701_0015, g32p_row07_traceSegment_002_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1731 15 15, g32p_row07_traceSegment_002_1731_0015, g32p_row07_traceSegment_002_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_002 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1701 30 30, g32p_row07_traceSegment_002_1701_0030, g32p_row07_traceSegment_002_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1761 15 15, g32p_row07_traceSegment_002_1761_0015, g32p_row07_traceSegment_002_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1791 15 16, g32p_row07_traceSegment_002_1791_0015, g32p_row07_traceSegment_002_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1761 30 31, g32p_row07_traceSegment_002_1761_0030, g32p_row07_traceSegment_002_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_002 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1701 60 61, g32p_row07_traceSegment_002_1701_0060, g32p_row07_traceSegment_002_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1822 15 15, g32p_row07_traceSegment_002_1822_0015, g32p_row07_traceSegment_002_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1852 15 16, g32p_row07_traceSegment_002_1852_0015, g32p_row07_traceSegment_002_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1822 30 31, g32p_row07_traceSegment_002_1822_0030, g32p_row07_traceSegment_002_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_002 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1883 15 15, g32p_row07_traceSegment_002_1883_0015, g32p_row07_traceSegment_002_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_002 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_002 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_002_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_002 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1913 15 16, g32p_row07_traceSegment_002_1913_0015, g32p_row07_traceSegment_002_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_002 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1883 30 31, g32p_row07_traceSegment_002_1883_0030, g32p_row07_traceSegment_002_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_002 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1822 61 61, g32p_row07_traceSegment_002_1822_0061, g32p_row07_traceSegment_002_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_002 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1701 121 122, g32p_row07_traceSegment_002_1701_0121, g32p_row07_traceSegment_002_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_002_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_002 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 1458 243 243, g32p_row07_traceSegment_002_1458_0243, g32p_row07_traceSegment_002_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_002 972 972 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 972 486 486, g32p_row07_traceSegment_002_0972_0486, g32p_row07_traceSegment_002_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_002_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_002 0 1944 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_002 0 972 972, g32p_row07_traceSegment_002_0000_0972, g32p_row07_traceSegment_002_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 2 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_002_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_004 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 4 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_004_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 0 15 15, g32p_row07_traceSegment_004_0000_0015, g32p_row07_traceSegment_004_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 30 15 15, g32p_row07_traceSegment_004_0030_0015, g32p_row07_traceSegment_004_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_004 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 0 30 30, g32p_row07_traceSegment_004_0000_0030, g32p_row07_traceSegment_004_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 60 15 15, g32p_row07_traceSegment_004_0060_0015, g32p_row07_traceSegment_004_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 90 15 16, g32p_row07_traceSegment_004_0090_0015, g32p_row07_traceSegment_004_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 60 30 31, g32p_row07_traceSegment_004_0060_0030, g32p_row07_traceSegment_004_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_004 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 0 60 61, g32p_row07_traceSegment_004_0000_0060, g32p_row07_traceSegment_004_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 121 15 15, g32p_row07_traceSegment_004_0121_0015, g32p_row07_traceSegment_004_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 151 15 16, g32p_row07_traceSegment_004_0151_0015, g32p_row07_traceSegment_004_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 121 30 31, g32p_row07_traceSegment_004_0121_0030, g32p_row07_traceSegment_004_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 182 15 15, g32p_row07_traceSegment_004_0182_0015, g32p_row07_traceSegment_004_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 212 15 16, g32p_row07_traceSegment_004_0212_0015, g32p_row07_traceSegment_004_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 182 30 31, g32p_row07_traceSegment_004_0182_0030, g32p_row07_traceSegment_004_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_004 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 121 61 61, g32p_row07_traceSegment_004_0121_0061, g32p_row07_traceSegment_004_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_004 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 0 121 122, g32p_row07_traceSegment_004_0000_0121, g32p_row07_traceSegment_004_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 243 15 15, g32p_row07_traceSegment_004_0243_0015, g32p_row07_traceSegment_004_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 273 15 15, g32p_row07_traceSegment_004_0273_0015, g32p_row07_traceSegment_004_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_004 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 243 30 30, g32p_row07_traceSegment_004_0243_0030, g32p_row07_traceSegment_004_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 303 15 15, g32p_row07_traceSegment_004_0303_0015, g32p_row07_traceSegment_004_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 333 15 16, g32p_row07_traceSegment_004_0333_0015, g32p_row07_traceSegment_004_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 303 30 31, g32p_row07_traceSegment_004_0303_0030, g32p_row07_traceSegment_004_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_004 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 243 60 61, g32p_row07_traceSegment_004_0243_0060, g32p_row07_traceSegment_004_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 364 15 15, g32p_row07_traceSegment_004_0364_0015, g32p_row07_traceSegment_004_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 394 15 16, g32p_row07_traceSegment_004_0394_0015, g32p_row07_traceSegment_004_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 364 30 31, g32p_row07_traceSegment_004_0364_0030, g32p_row07_traceSegment_004_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 425 15 15, g32p_row07_traceSegment_004_0425_0015, g32p_row07_traceSegment_004_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 455 15 16, g32p_row07_traceSegment_004_0455_0015, g32p_row07_traceSegment_004_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 425 30 31, g32p_row07_traceSegment_004_0425_0030, g32p_row07_traceSegment_004_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_004 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 364 61 61, g32p_row07_traceSegment_004_0364_0061, g32p_row07_traceSegment_004_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_004 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 243 121 122, g32p_row07_traceSegment_004_0243_0121, g32p_row07_traceSegment_004_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_004 0 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 0 243 243, g32p_row07_traceSegment_004_0000_0243, g32p_row07_traceSegment_004_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 486 15 15, g32p_row07_traceSegment_004_0486_0015, g32p_row07_traceSegment_004_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 516 15 15, g32p_row07_traceSegment_004_0516_0015, g32p_row07_traceSegment_004_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_004 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 486 30 30, g32p_row07_traceSegment_004_0486_0030, g32p_row07_traceSegment_004_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 546 15 15, g32p_row07_traceSegment_004_0546_0015, g32p_row07_traceSegment_004_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 576 15 16, g32p_row07_traceSegment_004_0576_0015, g32p_row07_traceSegment_004_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 546 30 31, g32p_row07_traceSegment_004_0546_0030, g32p_row07_traceSegment_004_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_004 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 486 60 61, g32p_row07_traceSegment_004_0486_0060, g32p_row07_traceSegment_004_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 607 15 15, g32p_row07_traceSegment_004_0607_0015, g32p_row07_traceSegment_004_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 637 15 16, g32p_row07_traceSegment_004_0637_0015, g32p_row07_traceSegment_004_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 607 30 31, g32p_row07_traceSegment_004_0607_0030, g32p_row07_traceSegment_004_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 668 15 15, g32p_row07_traceSegment_004_0668_0015, g32p_row07_traceSegment_004_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 698 15 16, g32p_row07_traceSegment_004_0698_0015, g32p_row07_traceSegment_004_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 668 30 31, g32p_row07_traceSegment_004_0668_0030, g32p_row07_traceSegment_004_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_004 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 607 61 61, g32p_row07_traceSegment_004_0607_0061, g32p_row07_traceSegment_004_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_004 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 486 121 122, g32p_row07_traceSegment_004_0486_0121, g32p_row07_traceSegment_004_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 729 15 15, g32p_row07_traceSegment_004_0729_0015, g32p_row07_traceSegment_004_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 759 15 15, g32p_row07_traceSegment_004_0759_0015, g32p_row07_traceSegment_004_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_004 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 729 30 30, g32p_row07_traceSegment_004_0729_0030, g32p_row07_traceSegment_004_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 789 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 804 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 789 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 789 15 15, g32p_row07_traceSegment_004_0789_0015, g32p_row07_traceSegment_004_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 819 15 16, g32p_row07_traceSegment_004_0819_0015, g32p_row07_traceSegment_004_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 789 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 789 30 31, g32p_row07_traceSegment_004_0789_0030, g32p_row07_traceSegment_004_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_004 729 121 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 729 60 61, g32p_row07_traceSegment_004_0729_0060, g32p_row07_traceSegment_004_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 850 15 15, g32p_row07_traceSegment_004_0850_0015, g32p_row07_traceSegment_004_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 880 15 16, g32p_row07_traceSegment_004_0880_0015, g32p_row07_traceSegment_004_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 850 30 31, g32p_row07_traceSegment_004_0850_0030, g32p_row07_traceSegment_004_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 911 15 15, g32p_row07_traceSegment_004_0911_0015, g32p_row07_traceSegment_004_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 941 15 16, g32p_row07_traceSegment_004_0941_0015, g32p_row07_traceSegment_004_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 911 30 31, g32p_row07_traceSegment_004_0911_0030, g32p_row07_traceSegment_004_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_004 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 850 61 61, g32p_row07_traceSegment_004_0850_0061, g32p_row07_traceSegment_004_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_004 729 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 729 121 122, g32p_row07_traceSegment_004_0729_0121, g32p_row07_traceSegment_004_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_004 486 486 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 486 243 243, g32p_row07_traceSegment_004_0486_0243, g32p_row07_traceSegment_004_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_004 0 972 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 0 486 486, g32p_row07_traceSegment_004_0000_0486, g32p_row07_traceSegment_004_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 972 15 15, g32p_row07_traceSegment_004_0972_0015, g32p_row07_traceSegment_004_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1002 15 15, g32p_row07_traceSegment_004_1002_0015, g32p_row07_traceSegment_004_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_004 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 972 30 30, g32p_row07_traceSegment_004_0972_0030, g32p_row07_traceSegment_004_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1032 15 15, g32p_row07_traceSegment_004_1032_0015, g32p_row07_traceSegment_004_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1062 15 16, g32p_row07_traceSegment_004_1062_0015, g32p_row07_traceSegment_004_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1032 30 31, g32p_row07_traceSegment_004_1032_0030, g32p_row07_traceSegment_004_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_004 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 972 60 61, g32p_row07_traceSegment_004_0972_0060, g32p_row07_traceSegment_004_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1093 15 15, g32p_row07_traceSegment_004_1093_0015, g32p_row07_traceSegment_004_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1123 15 16, g32p_row07_traceSegment_004_1123_0015, g32p_row07_traceSegment_004_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1093 30 31, g32p_row07_traceSegment_004_1093_0030, g32p_row07_traceSegment_004_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1154 15 15, g32p_row07_traceSegment_004_1154_0015, g32p_row07_traceSegment_004_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1184 15 16, g32p_row07_traceSegment_004_1184_0015, g32p_row07_traceSegment_004_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1154 30 31, g32p_row07_traceSegment_004_1154_0030, g32p_row07_traceSegment_004_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_004 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1093 61 61, g32p_row07_traceSegment_004_1093_0061, g32p_row07_traceSegment_004_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_004 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 972 121 122, g32p_row07_traceSegment_004_0972_0121, g32p_row07_traceSegment_004_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1230 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1215 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1215 15 15, g32p_row07_traceSegment_004_1215_0015, g32p_row07_traceSegment_004_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1245 15 15, g32p_row07_traceSegment_004_1245_0015, g32p_row07_traceSegment_004_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_004 1215 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1215 30 30, g32p_row07_traceSegment_004_1215_0030, g32p_row07_traceSegment_004_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1275 15 15, g32p_row07_traceSegment_004_1275_0015, g32p_row07_traceSegment_004_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1305 15 16, g32p_row07_traceSegment_004_1305_0015, g32p_row07_traceSegment_004_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1275 30 31, g32p_row07_traceSegment_004_1275_0030, g32p_row07_traceSegment_004_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_004 1215 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1215 60 61, g32p_row07_traceSegment_004_1215_0060, g32p_row07_traceSegment_004_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1336 15 15, g32p_row07_traceSegment_004_1336_0015, g32p_row07_traceSegment_004_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1366 15 16, g32p_row07_traceSegment_004_1366_0015, g32p_row07_traceSegment_004_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1336 30 31, g32p_row07_traceSegment_004_1336_0030, g32p_row07_traceSegment_004_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1397 15 15, g32p_row07_traceSegment_004_1397_0015, g32p_row07_traceSegment_004_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1427 15 16, g32p_row07_traceSegment_004_1427_0015, g32p_row07_traceSegment_004_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1397 30 31, g32p_row07_traceSegment_004_1397_0030, g32p_row07_traceSegment_004_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_004 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1336 61 61, g32p_row07_traceSegment_004_1336_0061, g32p_row07_traceSegment_004_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_004 1215 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1215 121 122, g32p_row07_traceSegment_004_1215_0121, g32p_row07_traceSegment_004_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_004 972 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 972 243 243, g32p_row07_traceSegment_004_0972_0243, g32p_row07_traceSegment_004_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1458 15 15, g32p_row07_traceSegment_004_1458_0015, g32p_row07_traceSegment_004_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1488 15 15, g32p_row07_traceSegment_004_1488_0015, g32p_row07_traceSegment_004_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_004 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1458 30 30, g32p_row07_traceSegment_004_1458_0030, g32p_row07_traceSegment_004_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1518 15 15, g32p_row07_traceSegment_004_1518_0015, g32p_row07_traceSegment_004_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1548 15 16, g32p_row07_traceSegment_004_1548_0015, g32p_row07_traceSegment_004_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1518 30 31, g32p_row07_traceSegment_004_1518_0030, g32p_row07_traceSegment_004_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_004 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1458 60 61, g32p_row07_traceSegment_004_1458_0060, g32p_row07_traceSegment_004_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1579 15 15, g32p_row07_traceSegment_004_1579_0015, g32p_row07_traceSegment_004_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1609 15 16, g32p_row07_traceSegment_004_1609_0015, g32p_row07_traceSegment_004_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1579 30 31, g32p_row07_traceSegment_004_1579_0030, g32p_row07_traceSegment_004_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1640 15 15, g32p_row07_traceSegment_004_1640_0015, g32p_row07_traceSegment_004_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1670 15 16, g32p_row07_traceSegment_004_1670_0015, g32p_row07_traceSegment_004_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1640 30 31, g32p_row07_traceSegment_004_1640_0030, g32p_row07_traceSegment_004_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_004 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1579 61 61, g32p_row07_traceSegment_004_1579_0061, g32p_row07_traceSegment_004_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_004 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1458 121 122, g32p_row07_traceSegment_004_1458_0121, g32p_row07_traceSegment_004_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1701 15 15, g32p_row07_traceSegment_004_1701_0015, g32p_row07_traceSegment_004_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1731 15 15, g32p_row07_traceSegment_004_1731_0015, g32p_row07_traceSegment_004_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_004 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1701 30 30, g32p_row07_traceSegment_004_1701_0030, g32p_row07_traceSegment_004_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1761 15 15, g32p_row07_traceSegment_004_1761_0015, g32p_row07_traceSegment_004_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1791 15 16, g32p_row07_traceSegment_004_1791_0015, g32p_row07_traceSegment_004_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1761 30 31, g32p_row07_traceSegment_004_1761_0030, g32p_row07_traceSegment_004_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_004 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1701 60 61, g32p_row07_traceSegment_004_1701_0060, g32p_row07_traceSegment_004_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1822 15 15, g32p_row07_traceSegment_004_1822_0015, g32p_row07_traceSegment_004_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1852 15 16, g32p_row07_traceSegment_004_1852_0015, g32p_row07_traceSegment_004_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1822 30 31, g32p_row07_traceSegment_004_1822_0030, g32p_row07_traceSegment_004_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_004 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1883 15 15, g32p_row07_traceSegment_004_1883_0015, g32p_row07_traceSegment_004_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_004 1913 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_004 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_004_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_004 1913 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1913 15 16, g32p_row07_traceSegment_004_1913_0015, g32p_row07_traceSegment_004_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_004 1883 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1883 30 31, g32p_row07_traceSegment_004_1883_0030, g32p_row07_traceSegment_004_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_004 1822 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1822 61 61, g32p_row07_traceSegment_004_1822_0061, g32p_row07_traceSegment_004_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_004 1701 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1701 121 122, g32p_row07_traceSegment_004_1701_0121, g32p_row07_traceSegment_004_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_004_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_004 1458 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 1458 243 243, g32p_row07_traceSegment_004_1458_0243, g32p_row07_traceSegment_004_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_004 972 972 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 972 486 486, g32p_row07_traceSegment_004_0972_0486, g32p_row07_traceSegment_004_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_004_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_004 0 1944 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_004 0 972 972, g32p_row07_traceSegment_004_0000_0972, g32p_row07_traceSegment_004_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 4 = [0, 0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_004_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_006 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 6 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_006_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 0 15 15, g32p_row07_traceSegment_006_0000_0015, g32p_row07_traceSegment_006_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 30 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 45 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 30 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 30 15 15, g32p_row07_traceSegment_006_0030_0015, g32p_row07_traceSegment_006_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_006 0 60 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 0 30 30, g32p_row07_traceSegment_006_0000_0030, g32p_row07_traceSegment_006_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 60 15 15, g32p_row07_traceSegment_006_0060_0015, g32p_row07_traceSegment_006_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 90 15 16, g32p_row07_traceSegment_006_0090_0015, g32p_row07_traceSegment_006_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 60 30 31, g32p_row07_traceSegment_006_0060_0030, g32p_row07_traceSegment_006_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_006 0 121 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 0 60 61, g32p_row07_traceSegment_006_0000_0060, g32p_row07_traceSegment_006_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 121 15 15, g32p_row07_traceSegment_006_0121_0015, g32p_row07_traceSegment_006_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 151 15 16, g32p_row07_traceSegment_006_0151_0015, g32p_row07_traceSegment_006_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 121 30 31, g32p_row07_traceSegment_006_0121_0030, g32p_row07_traceSegment_006_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 182 15 15, g32p_row07_traceSegment_006_0182_0015, g32p_row07_traceSegment_006_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 212 15 16, g32p_row07_traceSegment_006_0212_0015, g32p_row07_traceSegment_006_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 182 30 31, g32p_row07_traceSegment_006_0182_0030, g32p_row07_traceSegment_006_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_006 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 121 61 61, g32p_row07_traceSegment_006_0121_0061, g32p_row07_traceSegment_006_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_006 0 243 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 0 121 122, g32p_row07_traceSegment_006_0000_0121, g32p_row07_traceSegment_006_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 243 15 15, g32p_row07_traceSegment_006_0243_0015, g32p_row07_traceSegment_006_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 273 15 15, g32p_row07_traceSegment_006_0273_0015, g32p_row07_traceSegment_006_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_006 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 243 30 30, g32p_row07_traceSegment_006_0243_0030, g32p_row07_traceSegment_006_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 303 15 15, g32p_row07_traceSegment_006_0303_0015, g32p_row07_traceSegment_006_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 333 15 16, g32p_row07_traceSegment_006_0333_0015, g32p_row07_traceSegment_006_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 303 30 31, g32p_row07_traceSegment_006_0303_0030, g32p_row07_traceSegment_006_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_006 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 243 60 61, g32p_row07_traceSegment_006_0243_0060, g32p_row07_traceSegment_006_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 379 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 364 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 364 15 15, g32p_row07_traceSegment_006_0364_0015, g32p_row07_traceSegment_006_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 394 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 409 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 394 31 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 394 15 16, g32p_row07_traceSegment_006_0394_0015, g32p_row07_traceSegment_006_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 364 61 = [11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 364 30 31, g32p_row07_traceSegment_006_0364_0030, g32p_row07_traceSegment_006_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 440 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 425 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 425 15 15, g32p_row07_traceSegment_006_0425_0015, g32p_row07_traceSegment_006_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 455 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 470 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 455 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 455 15 16, g32p_row07_traceSegment_006_0455_0015, g32p_row07_traceSegment_006_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 425 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 425 30 31, g32p_row07_traceSegment_006_0425_0030, g32p_row07_traceSegment_006_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_006 364 122 = [14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 364 61 61, g32p_row07_traceSegment_006_0364_0061, g32p_row07_traceSegment_006_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_006 243 243 = [14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 243 121 122, g32p_row07_traceSegment_006_0243_0121, g32p_row07_traceSegment_006_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_006 0 486 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 0 243 243, g32p_row07_traceSegment_006_0000_0243, g32p_row07_traceSegment_006_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 486 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 501 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 486 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 486 15 15, g32p_row07_traceSegment_006_0486_0015, g32p_row07_traceSegment_006_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 516 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 531 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 516 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 516 15 15, g32p_row07_traceSegment_006_0516_0015, g32p_row07_traceSegment_006_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_006 486 60 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 486 30 30, g32p_row07_traceSegment_006_0486_0030, g32p_row07_traceSegment_006_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 546 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 561 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 546 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 546 15 15, g32p_row07_traceSegment_006_0546_0015, g32p_row07_traceSegment_006_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 576 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 591 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 576 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 576 15 16, g32p_row07_traceSegment_006_0576_0015, g32p_row07_traceSegment_006_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 546 61 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 546 30 31, g32p_row07_traceSegment_006_0546_0030, g32p_row07_traceSegment_006_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_006 486 121 = [12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 486 60 61, g32p_row07_traceSegment_006_0486_0060, g32p_row07_traceSegment_006_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 607 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 622 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 607 30 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 607 15 15, g32p_row07_traceSegment_006_0607_0015, g32p_row07_traceSegment_006_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 637 15 = [7] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 652 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 637 31 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 637 15 16, g32p_row07_traceSegment_006_0637_0015, g32p_row07_traceSegment_006_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 607 61 = [16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 607 30 31, g32p_row07_traceSegment_006_0607_0030, g32p_row07_traceSegment_006_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 668 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 683 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 668 30 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 668 15 15, g32p_row07_traceSegment_006_0668_0015, g32p_row07_traceSegment_006_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 698 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 713 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 698 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 698 15 16, g32p_row07_traceSegment_006_0698_0015, g32p_row07_traceSegment_006_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 668 61 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 668 30 31, g32p_row07_traceSegment_006_0668_0030, g32p_row07_traceSegment_006_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_006 607 122 = [24] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 607 61 61, g32p_row07_traceSegment_006_0607_0061, g32p_row07_traceSegment_006_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_006 486 243 = [36] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 486 121 122, g32p_row07_traceSegment_006_0486_0121, g32p_row07_traceSegment_006_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 729 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 744 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 729 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 729 15 15, g32p_row07_traceSegment_006_0729_0015, g32p_row07_traceSegment_006_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 759 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 759 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 759 15 15, g32p_row07_traceSegment_006_0759_0015, g32p_row07_traceSegment_006_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_006 729 60 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 729 30 30, g32p_row07_traceSegment_006_0729_0030, g32p_row07_traceSegment_006_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 789 15 15, g32p_row07_traceSegment_006_0789_0015, g32p_row07_traceSegment_006_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 819 15 16, g32p_row07_traceSegment_006_0819_0015, g32p_row07_traceSegment_006_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 789 30 31, g32p_row07_traceSegment_006_0789_0030, g32p_row07_traceSegment_006_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_006 729 121 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 729 60 61, g32p_row07_traceSegment_006_0729_0060, g32p_row07_traceSegment_006_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 850 15 15, g32p_row07_traceSegment_006_0850_0015, g32p_row07_traceSegment_006_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 880 15 16, g32p_row07_traceSegment_006_0880_0015, g32p_row07_traceSegment_006_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 850 30 31, g32p_row07_traceSegment_006_0850_0030, g32p_row07_traceSegment_006_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 911 15 15, g32p_row07_traceSegment_006_0911_0015, g32p_row07_traceSegment_006_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 941 15 16, g32p_row07_traceSegment_006_0941_0015, g32p_row07_traceSegment_006_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 911 30 31, g32p_row07_traceSegment_006_0911_0030, g32p_row07_traceSegment_006_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_006 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 850 61 61, g32p_row07_traceSegment_006_0850_0061, g32p_row07_traceSegment_006_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_006 729 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 729 121 122, g32p_row07_traceSegment_006_0729_0121, g32p_row07_traceSegment_006_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_006 486 486 = [41] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 486 243 243, g32p_row07_traceSegment_006_0486_0243, g32p_row07_traceSegment_006_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_006 0 972 = [59] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 0 486 486, g32p_row07_traceSegment_006_0000_0486, g32p_row07_traceSegment_006_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 972 15 15, g32p_row07_traceSegment_006_0972_0015, g32p_row07_traceSegment_006_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1002 15 15, g32p_row07_traceSegment_006_1002_0015, g32p_row07_traceSegment_006_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_006 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 972 30 30, g32p_row07_traceSegment_006_0972_0030, g32p_row07_traceSegment_006_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1032 15 15, g32p_row07_traceSegment_006_1032_0015, g32p_row07_traceSegment_006_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1062 15 16, g32p_row07_traceSegment_006_1062_0015, g32p_row07_traceSegment_006_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1032 30 31, g32p_row07_traceSegment_006_1032_0030, g32p_row07_traceSegment_006_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_006 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 972 60 61, g32p_row07_traceSegment_006_0972_0060, g32p_row07_traceSegment_006_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1093 15 15, g32p_row07_traceSegment_006_1093_0015, g32p_row07_traceSegment_006_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1123 15 16, g32p_row07_traceSegment_006_1123_0015, g32p_row07_traceSegment_006_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1093 30 31, g32p_row07_traceSegment_006_1093_0030, g32p_row07_traceSegment_006_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1154 15 15, g32p_row07_traceSegment_006_1154_0015, g32p_row07_traceSegment_006_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1184 15 16, g32p_row07_traceSegment_006_1184_0015, g32p_row07_traceSegment_006_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1154 30 31, g32p_row07_traceSegment_006_1154_0030, g32p_row07_traceSegment_006_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_006 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1093 61 61, g32p_row07_traceSegment_006_1093_0061, g32p_row07_traceSegment_006_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_006 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 972 121 122, g32p_row07_traceSegment_006_0972_0121, g32p_row07_traceSegment_006_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1215 15 15, g32p_row07_traceSegment_006_1215_0015, g32p_row07_traceSegment_006_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1245 15 15, g32p_row07_traceSegment_006_1245_0015, g32p_row07_traceSegment_006_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_006 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1215 30 30, g32p_row07_traceSegment_006_1215_0030, g32p_row07_traceSegment_006_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1275 15 15, g32p_row07_traceSegment_006_1275_0015, g32p_row07_traceSegment_006_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1305 15 16, g32p_row07_traceSegment_006_1305_0015, g32p_row07_traceSegment_006_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1275 30 31, g32p_row07_traceSegment_006_1275_0030, g32p_row07_traceSegment_006_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_006 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1215 60 61, g32p_row07_traceSegment_006_1215_0060, g32p_row07_traceSegment_006_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1336 15 15, g32p_row07_traceSegment_006_1336_0015, g32p_row07_traceSegment_006_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1366 15 16, g32p_row07_traceSegment_006_1366_0015, g32p_row07_traceSegment_006_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1336 30 31, g32p_row07_traceSegment_006_1336_0030, g32p_row07_traceSegment_006_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1397 15 15, g32p_row07_traceSegment_006_1397_0015, g32p_row07_traceSegment_006_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1427 15 16, g32p_row07_traceSegment_006_1427_0015, g32p_row07_traceSegment_006_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1397 30 31, g32p_row07_traceSegment_006_1397_0030, g32p_row07_traceSegment_006_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_006 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1336 61 61, g32p_row07_traceSegment_006_1336_0061, g32p_row07_traceSegment_006_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_006 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1215 121 122, g32p_row07_traceSegment_006_1215_0121, g32p_row07_traceSegment_006_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_006 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 972 243 243, g32p_row07_traceSegment_006_0972_0243, g32p_row07_traceSegment_006_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1458 15 15, g32p_row07_traceSegment_006_1458_0015, g32p_row07_traceSegment_006_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1488 15 15, g32p_row07_traceSegment_006_1488_0015, g32p_row07_traceSegment_006_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_006 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1458 30 30, g32p_row07_traceSegment_006_1458_0030, g32p_row07_traceSegment_006_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1518 15 15, g32p_row07_traceSegment_006_1518_0015, g32p_row07_traceSegment_006_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1548 15 16, g32p_row07_traceSegment_006_1548_0015, g32p_row07_traceSegment_006_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1518 30 31, g32p_row07_traceSegment_006_1518_0030, g32p_row07_traceSegment_006_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_006 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1458 60 61, g32p_row07_traceSegment_006_1458_0060, g32p_row07_traceSegment_006_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1579 15 15, g32p_row07_traceSegment_006_1579_0015, g32p_row07_traceSegment_006_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1609 15 16, g32p_row07_traceSegment_006_1609_0015, g32p_row07_traceSegment_006_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1579 30 31, g32p_row07_traceSegment_006_1579_0030, g32p_row07_traceSegment_006_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1640 15 15, g32p_row07_traceSegment_006_1640_0015, g32p_row07_traceSegment_006_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1670 15 16, g32p_row07_traceSegment_006_1670_0015, g32p_row07_traceSegment_006_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1640 30 31, g32p_row07_traceSegment_006_1640_0030, g32p_row07_traceSegment_006_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_006 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1579 61 61, g32p_row07_traceSegment_006_1579_0061, g32p_row07_traceSegment_006_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_006 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1458 121 122, g32p_row07_traceSegment_006_1458_0121, g32p_row07_traceSegment_006_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1701 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1701 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1701 15 15, g32p_row07_traceSegment_006_1701_0015, g32p_row07_traceSegment_006_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1731 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1746 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1731 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1731 15 15, g32p_row07_traceSegment_006_1731_0015, g32p_row07_traceSegment_006_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_006 1701 60 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1701 30 30, g32p_row07_traceSegment_006_1701_0030, g32p_row07_traceSegment_006_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1761 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1776 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1761 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1761 15 15, g32p_row07_traceSegment_006_1761_0015, g32p_row07_traceSegment_006_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1791 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1806 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1791 31 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1791 15 16, g32p_row07_traceSegment_006_1791_0015, g32p_row07_traceSegment_006_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1761 61 = [11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1761 30 31, g32p_row07_traceSegment_006_1761_0030, g32p_row07_traceSegment_006_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_006 1701 121 = [16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1701 60 61, g32p_row07_traceSegment_006_1701_0060, g32p_row07_traceSegment_006_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1822 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1837 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1822 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1822 15 15, g32p_row07_traceSegment_006_1822_0015, g32p_row07_traceSegment_006_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1852 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1867 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1852 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1852 15 16, g32p_row07_traceSegment_006_1852_0015, g32p_row07_traceSegment_006_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1822 61 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1822 30 31, g32p_row07_traceSegment_006_1822_0030, g32p_row07_traceSegment_006_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1883 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_006 1883 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1883 15 15, g32p_row07_traceSegment_006_1883_0015, g32p_row07_traceSegment_006_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_006 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_006 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_006_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_006 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1913 15 16, g32p_row07_traceSegment_006_1913_0015, g32p_row07_traceSegment_006_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_006 1883 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1883 30 31, g32p_row07_traceSegment_006_1883_0030, g32p_row07_traceSegment_006_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_006 1822 122 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1822 61 61, g32p_row07_traceSegment_006_1822_0061, g32p_row07_traceSegment_006_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_006 1701 243 = [25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1701 121 122, g32p_row07_traceSegment_006_1701_0121, g32p_row07_traceSegment_006_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_006_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_006 1458 486 = [25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 1458 243 243, g32p_row07_traceSegment_006_1458_0243, g32p_row07_traceSegment_006_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_006 972 972 = [25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 972 486 486, g32p_row07_traceSegment_006_0972_0486, g32p_row07_traceSegment_006_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_006_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_006 0 1944 = [84] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_006 0 972 972, g32p_row07_traceSegment_006_0000_0972, g32p_row07_traceSegment_006_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 6 = [84] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_006_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_009 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 9 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_009_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 15 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 0 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 0 15 15, g32p_row07_traceSegment_009_0000_0015, g32p_row07_traceSegment_009_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 30 15 15, g32p_row07_traceSegment_009_0030_0015, g32p_row07_traceSegment_009_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_009 0 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 0 30 30, g32p_row07_traceSegment_009_0000_0030, g32p_row07_traceSegment_009_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 60 15 15, g32p_row07_traceSegment_009_0060_0015, g32p_row07_traceSegment_009_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 90 15 16, g32p_row07_traceSegment_009_0090_0015, g32p_row07_traceSegment_009_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 60 30 31, g32p_row07_traceSegment_009_0060_0030, g32p_row07_traceSegment_009_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_009 0 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 0 60 61, g32p_row07_traceSegment_009_0000_0060, g32p_row07_traceSegment_009_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 121 15 15, g32p_row07_traceSegment_009_0121_0015, g32p_row07_traceSegment_009_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 151 15 16, g32p_row07_traceSegment_009_0151_0015, g32p_row07_traceSegment_009_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 121 30 31, g32p_row07_traceSegment_009_0121_0030, g32p_row07_traceSegment_009_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 182 15 15, g32p_row07_traceSegment_009_0182_0015, g32p_row07_traceSegment_009_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 212 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 227 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 212 31 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 212 15 16, g32p_row07_traceSegment_009_0212_0015, g32p_row07_traceSegment_009_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 182 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 182 30 31, g32p_row07_traceSegment_009_0182_0030, g32p_row07_traceSegment_009_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_009 121 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 121 61 61, g32p_row07_traceSegment_009_0121_0061, g32p_row07_traceSegment_009_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_009 0 243 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 0 121 122, g32p_row07_traceSegment_009_0000_0121, g32p_row07_traceSegment_009_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 243 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 243 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 243 15 15, g32p_row07_traceSegment_009_0243_0015, g32p_row07_traceSegment_009_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 273 15 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 288 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 273 30 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 273 15 15, g32p_row07_traceSegment_009_0273_0015, g32p_row07_traceSegment_009_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_009 243 60 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 243 30 30, g32p_row07_traceSegment_009_0243_0030, g32p_row07_traceSegment_009_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 303 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 318 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 303 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 303 15 15, g32p_row07_traceSegment_009_0303_0015, g32p_row07_traceSegment_009_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 333 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 348 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 333 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 333 15 16, g32p_row07_traceSegment_009_0333_0015, g32p_row07_traceSegment_009_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 303 61 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 303 30 31, g32p_row07_traceSegment_009_0303_0030, g32p_row07_traceSegment_009_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_009 243 121 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 243 60 61, g32p_row07_traceSegment_009_0243_0060, g32p_row07_traceSegment_009_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 364 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 364 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 364 15 15, g32p_row07_traceSegment_009_0364_0015, g32p_row07_traceSegment_009_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 394 15 16, g32p_row07_traceSegment_009_0394_0015, g32p_row07_traceSegment_009_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 364 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 364 30 31, g32p_row07_traceSegment_009_0364_0030, g32p_row07_traceSegment_009_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 425 15 15, g32p_row07_traceSegment_009_0425_0015, g32p_row07_traceSegment_009_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 455 15 16, g32p_row07_traceSegment_009_0455_0015, g32p_row07_traceSegment_009_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 425 30 31, g32p_row07_traceSegment_009_0425_0030, g32p_row07_traceSegment_009_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_009 364 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 364 61 61, g32p_row07_traceSegment_009_0364_0061, g32p_row07_traceSegment_009_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_009 243 243 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 243 121 122, g32p_row07_traceSegment_009_0243_0121, g32p_row07_traceSegment_009_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_009 0 486 = [0, 23] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 0 243 243, g32p_row07_traceSegment_009_0000_0243, g32p_row07_traceSegment_009_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 486 15 15, g32p_row07_traceSegment_009_0486_0015, g32p_row07_traceSegment_009_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 516 15 15, g32p_row07_traceSegment_009_0516_0015, g32p_row07_traceSegment_009_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_009 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 486 30 30, g32p_row07_traceSegment_009_0486_0030, g32p_row07_traceSegment_009_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 546 15 15, g32p_row07_traceSegment_009_0546_0015, g32p_row07_traceSegment_009_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 576 15 16, g32p_row07_traceSegment_009_0576_0015, g32p_row07_traceSegment_009_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 546 30 31, g32p_row07_traceSegment_009_0546_0030, g32p_row07_traceSegment_009_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_009 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 486 60 61, g32p_row07_traceSegment_009_0486_0060, g32p_row07_traceSegment_009_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 607 15 15, g32p_row07_traceSegment_009_0607_0015, g32p_row07_traceSegment_009_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 637 15 16, g32p_row07_traceSegment_009_0637_0015, g32p_row07_traceSegment_009_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 607 30 31, g32p_row07_traceSegment_009_0607_0030, g32p_row07_traceSegment_009_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 668 15 15, g32p_row07_traceSegment_009_0668_0015, g32p_row07_traceSegment_009_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 698 15 16, g32p_row07_traceSegment_009_0698_0015, g32p_row07_traceSegment_009_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 668 30 31, g32p_row07_traceSegment_009_0668_0030, g32p_row07_traceSegment_009_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_009 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 607 61 61, g32p_row07_traceSegment_009_0607_0061, g32p_row07_traceSegment_009_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_009 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 486 121 122, g32p_row07_traceSegment_009_0486_0121, g32p_row07_traceSegment_009_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 729 15 15, g32p_row07_traceSegment_009_0729_0015, g32p_row07_traceSegment_009_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 759 15 15, g32p_row07_traceSegment_009_0759_0015, g32p_row07_traceSegment_009_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_009 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 729 30 30, g32p_row07_traceSegment_009_0729_0030, g32p_row07_traceSegment_009_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 789 15 15, g32p_row07_traceSegment_009_0789_0015, g32p_row07_traceSegment_009_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 819 15 16, g32p_row07_traceSegment_009_0819_0015, g32p_row07_traceSegment_009_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 789 30 31, g32p_row07_traceSegment_009_0789_0030, g32p_row07_traceSegment_009_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_009 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 729 60 61, g32p_row07_traceSegment_009_0729_0060, g32p_row07_traceSegment_009_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 850 15 15, g32p_row07_traceSegment_009_0850_0015, g32p_row07_traceSegment_009_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 880 15 16, g32p_row07_traceSegment_009_0880_0015, g32p_row07_traceSegment_009_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 850 30 31, g32p_row07_traceSegment_009_0850_0030, g32p_row07_traceSegment_009_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 911 15 15, g32p_row07_traceSegment_009_0911_0015, g32p_row07_traceSegment_009_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 941 15 16, g32p_row07_traceSegment_009_0941_0015, g32p_row07_traceSegment_009_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 911 30 31, g32p_row07_traceSegment_009_0911_0030, g32p_row07_traceSegment_009_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_009 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 850 61 61, g32p_row07_traceSegment_009_0850_0061, g32p_row07_traceSegment_009_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_009 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 729 121 122, g32p_row07_traceSegment_009_0729_0121, g32p_row07_traceSegment_009_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_009 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 486 243 243, g32p_row07_traceSegment_009_0486_0243, g32p_row07_traceSegment_009_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_009 0 972 = [0, 23] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 0 486 486, g32p_row07_traceSegment_009_0000_0486, g32p_row07_traceSegment_009_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 972 15 15, g32p_row07_traceSegment_009_0972_0015, g32p_row07_traceSegment_009_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1002 15 15, g32p_row07_traceSegment_009_1002_0015, g32p_row07_traceSegment_009_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_009 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 972 30 30, g32p_row07_traceSegment_009_0972_0030, g32p_row07_traceSegment_009_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1032 15 15, g32p_row07_traceSegment_009_1032_0015, g32p_row07_traceSegment_009_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1062 15 16, g32p_row07_traceSegment_009_1062_0015, g32p_row07_traceSegment_009_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1032 30 31, g32p_row07_traceSegment_009_1032_0030, g32p_row07_traceSegment_009_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_009 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 972 60 61, g32p_row07_traceSegment_009_0972_0060, g32p_row07_traceSegment_009_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1093 15 15, g32p_row07_traceSegment_009_1093_0015, g32p_row07_traceSegment_009_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1123 15 16, g32p_row07_traceSegment_009_1123_0015, g32p_row07_traceSegment_009_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1093 30 31, g32p_row07_traceSegment_009_1093_0030, g32p_row07_traceSegment_009_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1154 15 15, g32p_row07_traceSegment_009_1154_0015, g32p_row07_traceSegment_009_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1184 15 16, g32p_row07_traceSegment_009_1184_0015, g32p_row07_traceSegment_009_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1154 30 31, g32p_row07_traceSegment_009_1154_0030, g32p_row07_traceSegment_009_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_009 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1093 61 61, g32p_row07_traceSegment_009_1093_0061, g32p_row07_traceSegment_009_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_009 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 972 121 122, g32p_row07_traceSegment_009_0972_0121, g32p_row07_traceSegment_009_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1215 15 15, g32p_row07_traceSegment_009_1215_0015, g32p_row07_traceSegment_009_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1245 15 15, g32p_row07_traceSegment_009_1245_0015, g32p_row07_traceSegment_009_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_009 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1215 30 30, g32p_row07_traceSegment_009_1215_0030, g32p_row07_traceSegment_009_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1275 15 15, g32p_row07_traceSegment_009_1275_0015, g32p_row07_traceSegment_009_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1305 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1320 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1305 31 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1305 15 16, g32p_row07_traceSegment_009_1305_0015, g32p_row07_traceSegment_009_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1275 61 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1275 30 31, g32p_row07_traceSegment_009_1275_0030, g32p_row07_traceSegment_009_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_009 1215 121 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1215 60 61, g32p_row07_traceSegment_009_1215_0060, g32p_row07_traceSegment_009_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1336 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1351 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1336 30 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1336 15 15, g32p_row07_traceSegment_009_1336_0015, g32p_row07_traceSegment_009_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1366 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1381 16 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1366 31 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1366 15 16, g32p_row07_traceSegment_009_1366_0015, g32p_row07_traceSegment_009_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1336 61 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1336 30 31, g32p_row07_traceSegment_009_1336_0030, g32p_row07_traceSegment_009_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1397 15 = [0, 7] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1412 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1397 30 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1397 15 15, g32p_row07_traceSegment_009_1397_0015, g32p_row07_traceSegment_009_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1427 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1442 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1427 31 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1427 15 16, g32p_row07_traceSegment_009_1427_0015, g32p_row07_traceSegment_009_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1397 61 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1397 30 31, g32p_row07_traceSegment_009_1397_0030, g32p_row07_traceSegment_009_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_009 1336 122 = [0, 28] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1336 61 61, g32p_row07_traceSegment_009_1336_0061, g32p_row07_traceSegment_009_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_009 1215 243 = [0, 34] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1215 121 122, g32p_row07_traceSegment_009_1215_0121, g32p_row07_traceSegment_009_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_009 972 486 = [0, 34] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 972 243 243, g32p_row07_traceSegment_009_0972_0243, g32p_row07_traceSegment_009_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1473 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1458 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1458 15 15, g32p_row07_traceSegment_009_1458_0015, g32p_row07_traceSegment_009_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1488 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1503 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1488 30 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1488 15 15, g32p_row07_traceSegment_009_1488_0015, g32p_row07_traceSegment_009_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_009 1458 60 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1458 30 30, g32p_row07_traceSegment_009_1458_0030, g32p_row07_traceSegment_009_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1518 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1518 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1518 15 15, g32p_row07_traceSegment_009_1518_0015, g32p_row07_traceSegment_009_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1548 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1548 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1548 15 16, g32p_row07_traceSegment_009_1548_0015, g32p_row07_traceSegment_009_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1518 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1518 30 31, g32p_row07_traceSegment_009_1518_0030, g32p_row07_traceSegment_009_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_009 1458 121 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1458 60 61, g32p_row07_traceSegment_009_1458_0060, g32p_row07_traceSegment_009_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1579 15 15, g32p_row07_traceSegment_009_1579_0015, g32p_row07_traceSegment_009_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1609 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1609 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1609 15 16, g32p_row07_traceSegment_009_1609_0015, g32p_row07_traceSegment_009_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1579 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1579 30 31, g32p_row07_traceSegment_009_1579_0030, g32p_row07_traceSegment_009_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1640 15 15, g32p_row07_traceSegment_009_1640_0015, g32p_row07_traceSegment_009_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1670 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1670 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1670 15 16, g32p_row07_traceSegment_009_1670_0015, g32p_row07_traceSegment_009_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1640 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1640 30 31, g32p_row07_traceSegment_009_1640_0030, g32p_row07_traceSegment_009_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_009 1579 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1579 61 61, g32p_row07_traceSegment_009_1579_0061, g32p_row07_traceSegment_009_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_009 1458 243 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1458 121 122, g32p_row07_traceSegment_009_1458_0121, g32p_row07_traceSegment_009_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1701 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1701 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1701 15 15, g32p_row07_traceSegment_009_1701_0015, g32p_row07_traceSegment_009_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1731 15 15, g32p_row07_traceSegment_009_1731_0015, g32p_row07_traceSegment_009_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_009 1701 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1701 30 30, g32p_row07_traceSegment_009_1701_0030, g32p_row07_traceSegment_009_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1761 15 15, g32p_row07_traceSegment_009_1761_0015, g32p_row07_traceSegment_009_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1791 15 16, g32p_row07_traceSegment_009_1791_0015, g32p_row07_traceSegment_009_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1761 30 31, g32p_row07_traceSegment_009_1761_0030, g32p_row07_traceSegment_009_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_009 1701 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1701 60 61, g32p_row07_traceSegment_009_1701_0060, g32p_row07_traceSegment_009_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1822 15 15, g32p_row07_traceSegment_009_1822_0015, g32p_row07_traceSegment_009_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1852 15 16, g32p_row07_traceSegment_009_1852_0015, g32p_row07_traceSegment_009_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1822 30 31, g32p_row07_traceSegment_009_1822_0030, g32p_row07_traceSegment_009_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_009 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1883 15 15, g32p_row07_traceSegment_009_1883_0015, g32p_row07_traceSegment_009_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_009 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_009 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_009_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_009 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1913 15 16, g32p_row07_traceSegment_009_1913_0015, g32p_row07_traceSegment_009_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_009 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1883 30 31, g32p_row07_traceSegment_009_1883_0030, g32p_row07_traceSegment_009_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_009 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1822 61 61, g32p_row07_traceSegment_009_1822_0061, g32p_row07_traceSegment_009_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_009 1701 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1701 121 122, g32p_row07_traceSegment_009_1701_0121, g32p_row07_traceSegment_009_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_009_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_009 1458 486 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 1458 243 243, g32p_row07_traceSegment_009_1458_0243, g32p_row07_traceSegment_009_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_009 972 972 = [0, 49] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 972 486 486, g32p_row07_traceSegment_009_0972_0486, g32p_row07_traceSegment_009_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_009_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_009 0 1944 = [0, 72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_009 0 972 972, g32p_row07_traceSegment_009_0000_0972, g32p_row07_traceSegment_009_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_009 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 9 = [0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_009_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_011 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 11 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_011_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 0 15 15, g32p_row07_traceSegment_011_0000_0015, g32p_row07_traceSegment_011_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 30 15 15, g32p_row07_traceSegment_011_0030_0015, g32p_row07_traceSegment_011_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_011 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 0 30 30, g32p_row07_traceSegment_011_0000_0030, g32p_row07_traceSegment_011_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 60 15 15, g32p_row07_traceSegment_011_0060_0015, g32p_row07_traceSegment_011_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 90 15 16, g32p_row07_traceSegment_011_0090_0015, g32p_row07_traceSegment_011_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 60 30 31, g32p_row07_traceSegment_011_0060_0030, g32p_row07_traceSegment_011_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_011 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 0 60 61, g32p_row07_traceSegment_011_0000_0060, g32p_row07_traceSegment_011_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 121 15 15, g32p_row07_traceSegment_011_0121_0015, g32p_row07_traceSegment_011_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 151 15 16, g32p_row07_traceSegment_011_0151_0015, g32p_row07_traceSegment_011_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 121 30 31, g32p_row07_traceSegment_011_0121_0030, g32p_row07_traceSegment_011_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 182 15 15, g32p_row07_traceSegment_011_0182_0015, g32p_row07_traceSegment_011_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 212 15 16, g32p_row07_traceSegment_011_0212_0015, g32p_row07_traceSegment_011_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 182 30 31, g32p_row07_traceSegment_011_0182_0030, g32p_row07_traceSegment_011_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_011 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 121 61 61, g32p_row07_traceSegment_011_0121_0061, g32p_row07_traceSegment_011_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_011 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 0 121 122, g32p_row07_traceSegment_011_0000_0121, g32p_row07_traceSegment_011_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 243 15 15, g32p_row07_traceSegment_011_0243_0015, g32p_row07_traceSegment_011_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 273 15 15, g32p_row07_traceSegment_011_0273_0015, g32p_row07_traceSegment_011_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_011 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 243 30 30, g32p_row07_traceSegment_011_0243_0030, g32p_row07_traceSegment_011_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 303 15 15, g32p_row07_traceSegment_011_0303_0015, g32p_row07_traceSegment_011_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 333 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 333 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 333 15 16, g32p_row07_traceSegment_011_0333_0015, g32p_row07_traceSegment_011_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 303 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 303 30 31, g32p_row07_traceSegment_011_0303_0030, g32p_row07_traceSegment_011_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_011 243 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 243 60 61, g32p_row07_traceSegment_011_0243_0060, g32p_row07_traceSegment_011_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 364 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 364 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 364 15 15, g32p_row07_traceSegment_011_0364_0015, g32p_row07_traceSegment_011_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 394 15 16, g32p_row07_traceSegment_011_0394_0015, g32p_row07_traceSegment_011_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 364 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 364 30 31, g32p_row07_traceSegment_011_0364_0030, g32p_row07_traceSegment_011_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 425 15 15, g32p_row07_traceSegment_011_0425_0015, g32p_row07_traceSegment_011_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 455 15 16, g32p_row07_traceSegment_011_0455_0015, g32p_row07_traceSegment_011_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 425 30 31, g32p_row07_traceSegment_011_0425_0030, g32p_row07_traceSegment_011_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_011 364 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 364 61 61, g32p_row07_traceSegment_011_0364_0061, g32p_row07_traceSegment_011_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_011 243 243 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 243 121 122, g32p_row07_traceSegment_011_0243_0121, g32p_row07_traceSegment_011_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_011 0 486 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 0 243 243, g32p_row07_traceSegment_011_0000_0243, g32p_row07_traceSegment_011_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 486 15 15, g32p_row07_traceSegment_011_0486_0015, g32p_row07_traceSegment_011_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 516 15 15, g32p_row07_traceSegment_011_0516_0015, g32p_row07_traceSegment_011_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_011 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 486 30 30, g32p_row07_traceSegment_011_0486_0030, g32p_row07_traceSegment_011_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 546 15 15, g32p_row07_traceSegment_011_0546_0015, g32p_row07_traceSegment_011_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 576 15 16, g32p_row07_traceSegment_011_0576_0015, g32p_row07_traceSegment_011_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 546 30 31, g32p_row07_traceSegment_011_0546_0030, g32p_row07_traceSegment_011_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_011 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 486 60 61, g32p_row07_traceSegment_011_0486_0060, g32p_row07_traceSegment_011_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 607 15 15, g32p_row07_traceSegment_011_0607_0015, g32p_row07_traceSegment_011_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 637 15 16, g32p_row07_traceSegment_011_0637_0015, g32p_row07_traceSegment_011_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 607 30 31, g32p_row07_traceSegment_011_0607_0030, g32p_row07_traceSegment_011_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 668 15 15, g32p_row07_traceSegment_011_0668_0015, g32p_row07_traceSegment_011_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 698 15 16, g32p_row07_traceSegment_011_0698_0015, g32p_row07_traceSegment_011_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 668 30 31, g32p_row07_traceSegment_011_0668_0030, g32p_row07_traceSegment_011_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_011 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 607 61 61, g32p_row07_traceSegment_011_0607_0061, g32p_row07_traceSegment_011_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_011 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 486 121 122, g32p_row07_traceSegment_011_0486_0121, g32p_row07_traceSegment_011_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 729 15 15, g32p_row07_traceSegment_011_0729_0015, g32p_row07_traceSegment_011_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 759 15 15, g32p_row07_traceSegment_011_0759_0015, g32p_row07_traceSegment_011_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_011 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 729 30 30, g32p_row07_traceSegment_011_0729_0030, g32p_row07_traceSegment_011_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 789 15 15, g32p_row07_traceSegment_011_0789_0015, g32p_row07_traceSegment_011_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 819 15 16, g32p_row07_traceSegment_011_0819_0015, g32p_row07_traceSegment_011_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 789 30 31, g32p_row07_traceSegment_011_0789_0030, g32p_row07_traceSegment_011_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_011 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 729 60 61, g32p_row07_traceSegment_011_0729_0060, g32p_row07_traceSegment_011_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 850 15 15, g32p_row07_traceSegment_011_0850_0015, g32p_row07_traceSegment_011_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 880 15 16, g32p_row07_traceSegment_011_0880_0015, g32p_row07_traceSegment_011_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 850 30 31, g32p_row07_traceSegment_011_0850_0030, g32p_row07_traceSegment_011_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 911 15 15, g32p_row07_traceSegment_011_0911_0015, g32p_row07_traceSegment_011_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 941 15 16, g32p_row07_traceSegment_011_0941_0015, g32p_row07_traceSegment_011_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 911 30 31, g32p_row07_traceSegment_011_0911_0030, g32p_row07_traceSegment_011_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_011 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 850 61 61, g32p_row07_traceSegment_011_0850_0061, g32p_row07_traceSegment_011_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_011 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 729 121 122, g32p_row07_traceSegment_011_0729_0121, g32p_row07_traceSegment_011_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_011 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 486 243 243, g32p_row07_traceSegment_011_0486_0243, g32p_row07_traceSegment_011_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_011 0 972 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 0 486 486, g32p_row07_traceSegment_011_0000_0486, g32p_row07_traceSegment_011_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 972 15 15, g32p_row07_traceSegment_011_0972_0015, g32p_row07_traceSegment_011_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1002 15 15, g32p_row07_traceSegment_011_1002_0015, g32p_row07_traceSegment_011_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_011 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 972 30 30, g32p_row07_traceSegment_011_0972_0030, g32p_row07_traceSegment_011_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1032 15 15, g32p_row07_traceSegment_011_1032_0015, g32p_row07_traceSegment_011_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1062 15 16, g32p_row07_traceSegment_011_1062_0015, g32p_row07_traceSegment_011_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1032 30 31, g32p_row07_traceSegment_011_1032_0030, g32p_row07_traceSegment_011_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_011 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 972 60 61, g32p_row07_traceSegment_011_0972_0060, g32p_row07_traceSegment_011_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1093 15 15, g32p_row07_traceSegment_011_1093_0015, g32p_row07_traceSegment_011_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1123 15 16, g32p_row07_traceSegment_011_1123_0015, g32p_row07_traceSegment_011_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1093 30 31, g32p_row07_traceSegment_011_1093_0030, g32p_row07_traceSegment_011_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1154 15 15, g32p_row07_traceSegment_011_1154_0015, g32p_row07_traceSegment_011_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1184 15 16, g32p_row07_traceSegment_011_1184_0015, g32p_row07_traceSegment_011_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1154 30 31, g32p_row07_traceSegment_011_1154_0030, g32p_row07_traceSegment_011_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_011 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1093 61 61, g32p_row07_traceSegment_011_1093_0061, g32p_row07_traceSegment_011_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_011 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 972 121 122, g32p_row07_traceSegment_011_0972_0121, g32p_row07_traceSegment_011_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1215 15 15, g32p_row07_traceSegment_011_1215_0015, g32p_row07_traceSegment_011_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1245 15 15, g32p_row07_traceSegment_011_1245_0015, g32p_row07_traceSegment_011_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_011 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1215 30 30, g32p_row07_traceSegment_011_1215_0030, g32p_row07_traceSegment_011_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1275 15 15, g32p_row07_traceSegment_011_1275_0015, g32p_row07_traceSegment_011_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1305 15 16, g32p_row07_traceSegment_011_1305_0015, g32p_row07_traceSegment_011_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1275 30 31, g32p_row07_traceSegment_011_1275_0030, g32p_row07_traceSegment_011_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_011 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1215 60 61, g32p_row07_traceSegment_011_1215_0060, g32p_row07_traceSegment_011_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1351 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1336 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1336 15 15, g32p_row07_traceSegment_011_1336_0015, g32p_row07_traceSegment_011_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1366 15 16, g32p_row07_traceSegment_011_1366_0015, g32p_row07_traceSegment_011_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1336 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1336 30 31, g32p_row07_traceSegment_011_1336_0030, g32p_row07_traceSegment_011_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1397 15 15, g32p_row07_traceSegment_011_1397_0015, g32p_row07_traceSegment_011_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1427 15 16, g32p_row07_traceSegment_011_1427_0015, g32p_row07_traceSegment_011_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1397 30 31, g32p_row07_traceSegment_011_1397_0030, g32p_row07_traceSegment_011_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_011 1336 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1336 61 61, g32p_row07_traceSegment_011_1336_0061, g32p_row07_traceSegment_011_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_011 1215 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1215 121 122, g32p_row07_traceSegment_011_1215_0121, g32p_row07_traceSegment_011_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_011 972 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 972 243 243, g32p_row07_traceSegment_011_0972_0243, g32p_row07_traceSegment_011_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1458 15 15, g32p_row07_traceSegment_011_1458_0015, g32p_row07_traceSegment_011_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1488 15 15, g32p_row07_traceSegment_011_1488_0015, g32p_row07_traceSegment_011_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_011 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1458 30 30, g32p_row07_traceSegment_011_1458_0030, g32p_row07_traceSegment_011_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1518 15 15, g32p_row07_traceSegment_011_1518_0015, g32p_row07_traceSegment_011_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1548 15 16, g32p_row07_traceSegment_011_1548_0015, g32p_row07_traceSegment_011_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1518 30 31, g32p_row07_traceSegment_011_1518_0030, g32p_row07_traceSegment_011_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_011 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1458 60 61, g32p_row07_traceSegment_011_1458_0060, g32p_row07_traceSegment_011_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1579 15 15, g32p_row07_traceSegment_011_1579_0015, g32p_row07_traceSegment_011_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1609 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1609 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1609 15 16, g32p_row07_traceSegment_011_1609_0015, g32p_row07_traceSegment_011_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1579 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1579 30 31, g32p_row07_traceSegment_011_1579_0030, g32p_row07_traceSegment_011_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1640 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1640 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1640 15 15, g32p_row07_traceSegment_011_1640_0015, g32p_row07_traceSegment_011_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1670 15 16, g32p_row07_traceSegment_011_1670_0015, g32p_row07_traceSegment_011_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1640 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1640 30 31, g32p_row07_traceSegment_011_1640_0030, g32p_row07_traceSegment_011_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_011 1579 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1579 61 61, g32p_row07_traceSegment_011_1579_0061, g32p_row07_traceSegment_011_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_011 1458 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1458 121 122, g32p_row07_traceSegment_011_1458_0121, g32p_row07_traceSegment_011_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1701 15 15, g32p_row07_traceSegment_011_1701_0015, g32p_row07_traceSegment_011_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1731 15 15, g32p_row07_traceSegment_011_1731_0015, g32p_row07_traceSegment_011_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_011 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1701 30 30, g32p_row07_traceSegment_011_1701_0030, g32p_row07_traceSegment_011_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1761 15 15, g32p_row07_traceSegment_011_1761_0015, g32p_row07_traceSegment_011_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1791 15 16, g32p_row07_traceSegment_011_1791_0015, g32p_row07_traceSegment_011_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1761 30 31, g32p_row07_traceSegment_011_1761_0030, g32p_row07_traceSegment_011_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_011 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1701 60 61, g32p_row07_traceSegment_011_1701_0060, g32p_row07_traceSegment_011_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1822 15 15, g32p_row07_traceSegment_011_1822_0015, g32p_row07_traceSegment_011_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1852 15 16, g32p_row07_traceSegment_011_1852_0015, g32p_row07_traceSegment_011_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1822 30 31, g32p_row07_traceSegment_011_1822_0030, g32p_row07_traceSegment_011_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_011 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1883 15 15, g32p_row07_traceSegment_011_1883_0015, g32p_row07_traceSegment_011_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_011 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_011 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_011_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_011 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1913 15 16, g32p_row07_traceSegment_011_1913_0015, g32p_row07_traceSegment_011_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_011 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1883 30 31, g32p_row07_traceSegment_011_1883_0030, g32p_row07_traceSegment_011_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_011 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1822 61 61, g32p_row07_traceSegment_011_1822_0061, g32p_row07_traceSegment_011_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_011 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1701 121 122, g32p_row07_traceSegment_011_1701_0121, g32p_row07_traceSegment_011_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_011_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_011 1458 486 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 1458 243 243, g32p_row07_traceSegment_011_1458_0243, g32p_row07_traceSegment_011_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_011 972 972 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 972 486 486, g32p_row07_traceSegment_011_0972_0486, g32p_row07_traceSegment_011_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_011_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_011 0 1944 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_011 0 972 972, g32p_row07_traceSegment_011_0000_0972, g32p_row07_traceSegment_011_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 11 = [0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_011_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_012 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 12 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_012_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 0 15 15, g32p_row07_traceSegment_012_0000_0015, g32p_row07_traceSegment_012_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 30 15 15, g32p_row07_traceSegment_012_0030_0015, g32p_row07_traceSegment_012_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_012 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 0 30 30, g32p_row07_traceSegment_012_0000_0030, g32p_row07_traceSegment_012_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 60 15 15, g32p_row07_traceSegment_012_0060_0015, g32p_row07_traceSegment_012_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 90 15 16, g32p_row07_traceSegment_012_0090_0015, g32p_row07_traceSegment_012_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 60 30 31, g32p_row07_traceSegment_012_0060_0030, g32p_row07_traceSegment_012_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_012 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 0 60 61, g32p_row07_traceSegment_012_0000_0060, g32p_row07_traceSegment_012_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 121 15 15, g32p_row07_traceSegment_012_0121_0015, g32p_row07_traceSegment_012_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 166 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 151 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 151 15 16, g32p_row07_traceSegment_012_0151_0015, g32p_row07_traceSegment_012_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 121 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 121 30 31, g32p_row07_traceSegment_012_0121_0030, g32p_row07_traceSegment_012_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 182 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 197 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 182 30 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 182 15 15, g32p_row07_traceSegment_012_0182_0015, g32p_row07_traceSegment_012_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 212 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 227 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 212 31 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 212 15 16, g32p_row07_traceSegment_012_0212_0015, g32p_row07_traceSegment_012_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 182 61 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 182 30 31, g32p_row07_traceSegment_012_0182_0030, g32p_row07_traceSegment_012_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_012 121 122 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 121 61 61, g32p_row07_traceSegment_012_0121_0061, g32p_row07_traceSegment_012_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_012 0 243 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 0 121 122, g32p_row07_traceSegment_012_0000_0121, g32p_row07_traceSegment_012_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 243 15 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 258 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 243 30 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 243 15 15, g32p_row07_traceSegment_012_0243_0015, g32p_row07_traceSegment_012_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 288 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 273 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 273 15 15, g32p_row07_traceSegment_012_0273_0015, g32p_row07_traceSegment_012_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_012 243 60 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 243 30 30, g32p_row07_traceSegment_012_0243_0030, g32p_row07_traceSegment_012_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 318 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 303 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 303 15 15, g32p_row07_traceSegment_012_0303_0015, g32p_row07_traceSegment_012_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 333 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 348 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 333 31 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 333 15 16, g32p_row07_traceSegment_012_0333_0015, g32p_row07_traceSegment_012_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 303 61 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 303 30 31, g32p_row07_traceSegment_012_0303_0030, g32p_row07_traceSegment_012_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_012 243 121 = [0, 19] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 243 60 61, g32p_row07_traceSegment_012_0243_0060, g32p_row07_traceSegment_012_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 364 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 364 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 364 15 15, g32p_row07_traceSegment_012_0364_0015, g32p_row07_traceSegment_012_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 394 15 16, g32p_row07_traceSegment_012_0394_0015, g32p_row07_traceSegment_012_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 364 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 364 30 31, g32p_row07_traceSegment_012_0364_0030, g32p_row07_traceSegment_012_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 425 15 15, g32p_row07_traceSegment_012_0425_0015, g32p_row07_traceSegment_012_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 455 15 16, g32p_row07_traceSegment_012_0455_0015, g32p_row07_traceSegment_012_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 425 30 31, g32p_row07_traceSegment_012_0425_0030, g32p_row07_traceSegment_012_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_012 364 122 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 364 61 61, g32p_row07_traceSegment_012_0364_0061, g32p_row07_traceSegment_012_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_012 243 243 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 243 121 122, g32p_row07_traceSegment_012_0243_0121, g32p_row07_traceSegment_012_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_012 0 486 = [0, 37] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 0 243 243, g32p_row07_traceSegment_012_0000_0243, g32p_row07_traceSegment_012_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 486 15 15, g32p_row07_traceSegment_012_0486_0015, g32p_row07_traceSegment_012_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 516 15 15, g32p_row07_traceSegment_012_0516_0015, g32p_row07_traceSegment_012_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_012 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 486 30 30, g32p_row07_traceSegment_012_0486_0030, g32p_row07_traceSegment_012_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 546 15 15, g32p_row07_traceSegment_012_0546_0015, g32p_row07_traceSegment_012_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 576 15 16, g32p_row07_traceSegment_012_0576_0015, g32p_row07_traceSegment_012_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 546 30 31, g32p_row07_traceSegment_012_0546_0030, g32p_row07_traceSegment_012_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_012 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 486 60 61, g32p_row07_traceSegment_012_0486_0060, g32p_row07_traceSegment_012_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 607 15 15, g32p_row07_traceSegment_012_0607_0015, g32p_row07_traceSegment_012_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 637 15 16, g32p_row07_traceSegment_012_0637_0015, g32p_row07_traceSegment_012_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 607 30 31, g32p_row07_traceSegment_012_0607_0030, g32p_row07_traceSegment_012_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 668 15 15, g32p_row07_traceSegment_012_0668_0015, g32p_row07_traceSegment_012_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 698 15 16, g32p_row07_traceSegment_012_0698_0015, g32p_row07_traceSegment_012_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 668 30 31, g32p_row07_traceSegment_012_0668_0030, g32p_row07_traceSegment_012_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_012 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 607 61 61, g32p_row07_traceSegment_012_0607_0061, g32p_row07_traceSegment_012_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_012 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 486 121 122, g32p_row07_traceSegment_012_0486_0121, g32p_row07_traceSegment_012_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 729 15 15, g32p_row07_traceSegment_012_0729_0015, g32p_row07_traceSegment_012_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 759 15 15, g32p_row07_traceSegment_012_0759_0015, g32p_row07_traceSegment_012_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_012 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 729 30 30, g32p_row07_traceSegment_012_0729_0030, g32p_row07_traceSegment_012_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 789 15 15, g32p_row07_traceSegment_012_0789_0015, g32p_row07_traceSegment_012_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 819 15 16, g32p_row07_traceSegment_012_0819_0015, g32p_row07_traceSegment_012_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 789 30 31, g32p_row07_traceSegment_012_0789_0030, g32p_row07_traceSegment_012_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_012 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 729 60 61, g32p_row07_traceSegment_012_0729_0060, g32p_row07_traceSegment_012_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 850 15 15, g32p_row07_traceSegment_012_0850_0015, g32p_row07_traceSegment_012_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 880 15 16, g32p_row07_traceSegment_012_0880_0015, g32p_row07_traceSegment_012_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 850 30 31, g32p_row07_traceSegment_012_0850_0030, g32p_row07_traceSegment_012_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 911 15 15, g32p_row07_traceSegment_012_0911_0015, g32p_row07_traceSegment_012_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 941 15 16, g32p_row07_traceSegment_012_0941_0015, g32p_row07_traceSegment_012_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 911 30 31, g32p_row07_traceSegment_012_0911_0030, g32p_row07_traceSegment_012_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_012 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 850 61 61, g32p_row07_traceSegment_012_0850_0061, g32p_row07_traceSegment_012_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_012 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 729 121 122, g32p_row07_traceSegment_012_0729_0121, g32p_row07_traceSegment_012_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_012 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 486 243 243, g32p_row07_traceSegment_012_0486_0243, g32p_row07_traceSegment_012_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_012 0 972 = [0, 37] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 0 486 486, g32p_row07_traceSegment_012_0000_0486, g32p_row07_traceSegment_012_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 972 15 15, g32p_row07_traceSegment_012_0972_0015, g32p_row07_traceSegment_012_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1002 15 15, g32p_row07_traceSegment_012_1002_0015, g32p_row07_traceSegment_012_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_012 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 972 30 30, g32p_row07_traceSegment_012_0972_0030, g32p_row07_traceSegment_012_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1032 15 15, g32p_row07_traceSegment_012_1032_0015, g32p_row07_traceSegment_012_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1062 15 16, g32p_row07_traceSegment_012_1062_0015, g32p_row07_traceSegment_012_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1032 30 31, g32p_row07_traceSegment_012_1032_0030, g32p_row07_traceSegment_012_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_012 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 972 60 61, g32p_row07_traceSegment_012_0972_0060, g32p_row07_traceSegment_012_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1093 15 15, g32p_row07_traceSegment_012_1093_0015, g32p_row07_traceSegment_012_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1123 15 16, g32p_row07_traceSegment_012_1123_0015, g32p_row07_traceSegment_012_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1093 30 31, g32p_row07_traceSegment_012_1093_0030, g32p_row07_traceSegment_012_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1154 15 15, g32p_row07_traceSegment_012_1154_0015, g32p_row07_traceSegment_012_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1184 15 16, g32p_row07_traceSegment_012_1184_0015, g32p_row07_traceSegment_012_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1154 30 31, g32p_row07_traceSegment_012_1154_0030, g32p_row07_traceSegment_012_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_012 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1093 61 61, g32p_row07_traceSegment_012_1093_0061, g32p_row07_traceSegment_012_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_012 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 972 121 122, g32p_row07_traceSegment_012_0972_0121, g32p_row07_traceSegment_012_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1215 15 15, g32p_row07_traceSegment_012_1215_0015, g32p_row07_traceSegment_012_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1245 15 15, g32p_row07_traceSegment_012_1245_0015, g32p_row07_traceSegment_012_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_012 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1215 30 30, g32p_row07_traceSegment_012_1215_0030, g32p_row07_traceSegment_012_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1275 15 15, g32p_row07_traceSegment_012_1275_0015, g32p_row07_traceSegment_012_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1305 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1305 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1305 15 16, g32p_row07_traceSegment_012_1305_0015, g32p_row07_traceSegment_012_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1275 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1275 30 31, g32p_row07_traceSegment_012_1275_0030, g32p_row07_traceSegment_012_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_012 1215 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1215 60 61, g32p_row07_traceSegment_012_1215_0060, g32p_row07_traceSegment_012_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1336 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1336 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1336 15 15, g32p_row07_traceSegment_012_1336_0015, g32p_row07_traceSegment_012_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1381 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1366 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1366 15 16, g32p_row07_traceSegment_012_1366_0015, g32p_row07_traceSegment_012_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1336 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1336 30 31, g32p_row07_traceSegment_012_1336_0030, g32p_row07_traceSegment_012_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1397 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1397 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1397 15 15, g32p_row07_traceSegment_012_1397_0015, g32p_row07_traceSegment_012_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1442 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1427 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1427 15 16, g32p_row07_traceSegment_012_1427_0015, g32p_row07_traceSegment_012_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1397 61 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1397 30 31, g32p_row07_traceSegment_012_1397_0030, g32p_row07_traceSegment_012_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_012 1336 122 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1336 61 61, g32p_row07_traceSegment_012_1336_0061, g32p_row07_traceSegment_012_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_012 1215 243 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1215 121 122, g32p_row07_traceSegment_012_1215_0121, g32p_row07_traceSegment_012_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_012 972 486 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 972 243 243, g32p_row07_traceSegment_012_0972_0243, g32p_row07_traceSegment_012_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1458 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1473 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1458 30 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1458 15 15, g32p_row07_traceSegment_012_1458_0015, g32p_row07_traceSegment_012_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1503 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1488 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1488 15 15, g32p_row07_traceSegment_012_1488_0015, g32p_row07_traceSegment_012_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_012 1458 60 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1458 30 30, g32p_row07_traceSegment_012_1458_0030, g32p_row07_traceSegment_012_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1518 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1533 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1518 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1518 15 15, g32p_row07_traceSegment_012_1518_0015, g32p_row07_traceSegment_012_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1548 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1563 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1548 31 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1548 15 16, g32p_row07_traceSegment_012_1548_0015, g32p_row07_traceSegment_012_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1518 61 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1518 30 31, g32p_row07_traceSegment_012_1518_0030, g32p_row07_traceSegment_012_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_012 1458 121 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1458 60 61, g32p_row07_traceSegment_012_1458_0060, g32p_row07_traceSegment_012_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1579 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1594 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1579 30 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1579 15 15, g32p_row07_traceSegment_012_1579_0015, g32p_row07_traceSegment_012_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1624 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1609 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1609 15 16, g32p_row07_traceSegment_012_1609_0015, g32p_row07_traceSegment_012_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1579 61 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1579 30 31, g32p_row07_traceSegment_012_1579_0030, g32p_row07_traceSegment_012_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1640 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1655 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1640 30 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1640 15 15, g32p_row07_traceSegment_012_1640_0015, g32p_row07_traceSegment_012_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1685 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1670 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1670 15 16, g32p_row07_traceSegment_012_1670_0015, g32p_row07_traceSegment_012_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1640 61 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1640 30 31, g32p_row07_traceSegment_012_1640_0030, g32p_row07_traceSegment_012_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_012 1579 122 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1579 61 61, g32p_row07_traceSegment_012_1579_0061, g32p_row07_traceSegment_012_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_012 1458 243 = [0, 27] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1458 121 122, g32p_row07_traceSegment_012_1458_0121, g32p_row07_traceSegment_012_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1701 15 15, g32p_row07_traceSegment_012_1701_0015, g32p_row07_traceSegment_012_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1731 15 15, g32p_row07_traceSegment_012_1731_0015, g32p_row07_traceSegment_012_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_012 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1701 30 30, g32p_row07_traceSegment_012_1701_0030, g32p_row07_traceSegment_012_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1761 15 15, g32p_row07_traceSegment_012_1761_0015, g32p_row07_traceSegment_012_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1791 15 16, g32p_row07_traceSegment_012_1791_0015, g32p_row07_traceSegment_012_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1761 30 31, g32p_row07_traceSegment_012_1761_0030, g32p_row07_traceSegment_012_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_012 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1701 60 61, g32p_row07_traceSegment_012_1701_0060, g32p_row07_traceSegment_012_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1822 15 15, g32p_row07_traceSegment_012_1822_0015, g32p_row07_traceSegment_012_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1852 15 16, g32p_row07_traceSegment_012_1852_0015, g32p_row07_traceSegment_012_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1822 30 31, g32p_row07_traceSegment_012_1822_0030, g32p_row07_traceSegment_012_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_012 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1883 15 15, g32p_row07_traceSegment_012_1883_0015, g32p_row07_traceSegment_012_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_012 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_012 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_012_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_012 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1913 15 16, g32p_row07_traceSegment_012_1913_0015, g32p_row07_traceSegment_012_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_012 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1883 30 31, g32p_row07_traceSegment_012_1883_0030, g32p_row07_traceSegment_012_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_012 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1822 61 61, g32p_row07_traceSegment_012_1822_0061, g32p_row07_traceSegment_012_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_012 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1701 121 122, g32p_row07_traceSegment_012_1701_0121, g32p_row07_traceSegment_012_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_012_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_012 1458 486 = [0, 27] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 1458 243 243, g32p_row07_traceSegment_012_1458_0243, g32p_row07_traceSegment_012_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_012 972 972 = [0, 35] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 972 486 486, g32p_row07_traceSegment_012_0972_0486, g32p_row07_traceSegment_012_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_012_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_012 0 1944 = [0, 72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_012 0 972 972, g32p_row07_traceSegment_012_0000_0972, g32p_row07_traceSegment_012_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_012 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 12 = [0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_012_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row07_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 0) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 0) (g32p_literalTraceValue 6 0)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_000]
  decide +kernel

theorem g32p_row07_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 1) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 1) (g32p_literalTraceValue 6 1)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_001]
  decide +kernel

theorem g32p_row07_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 2) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 2) (g32p_literalTraceValue 6 2)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row07_traceCoefficients_002]
  decide +kernel

theorem g32p_row07_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 4) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 4) (g32p_literalTraceValue 6 4)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row07_traceCoefficients_004]
  decide +kernel

theorem g32p_row07_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 6) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 6) (g32p_literalTraceValue 6 6)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_006]
  decide +kernel

theorem g32p_row07_tracePolynomial_009 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 9) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 9) (g32p_literalTraceValue 6 9)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_009]
  decide +kernel

theorem g32p_row07_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 11) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 11) (g32p_literalTraceValue 6 11)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_011]
  decide +kernel

theorem g32p_row07_tracePolynomial_012 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 12) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 12) (g32p_literalTraceValue 6 12)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_012]
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

private def g32p_row07_traceSegment_013 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 13 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_013_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 0 15 15, g32p_row07_traceSegment_013_0000_0015, g32p_row07_traceSegment_013_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 30 15 15, g32p_row07_traceSegment_013_0030_0015, g32p_row07_traceSegment_013_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_013 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 0 30 30, g32p_row07_traceSegment_013_0000_0030, g32p_row07_traceSegment_013_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 60 15 15, g32p_row07_traceSegment_013_0060_0015, g32p_row07_traceSegment_013_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 90 15 16, g32p_row07_traceSegment_013_0090_0015, g32p_row07_traceSegment_013_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 60 30 31, g32p_row07_traceSegment_013_0060_0030, g32p_row07_traceSegment_013_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_013 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 0 60 61, g32p_row07_traceSegment_013_0000_0060, g32p_row07_traceSegment_013_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 121 15 15, g32p_row07_traceSegment_013_0121_0015, g32p_row07_traceSegment_013_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 151 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 151 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 151 15 16, g32p_row07_traceSegment_013_0151_0015, g32p_row07_traceSegment_013_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 121 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 121 30 31, g32p_row07_traceSegment_013_0121_0030, g32p_row07_traceSegment_013_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 182 15 15, g32p_row07_traceSegment_013_0182_0015, g32p_row07_traceSegment_013_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 212 15 16, g32p_row07_traceSegment_013_0212_0015, g32p_row07_traceSegment_013_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 182 30 31, g32p_row07_traceSegment_013_0182_0030, g32p_row07_traceSegment_013_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_013 121 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 121 61 61, g32p_row07_traceSegment_013_0121_0061, g32p_row07_traceSegment_013_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_013 0 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 0 121 122, g32p_row07_traceSegment_013_0000_0121, g32p_row07_traceSegment_013_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 243 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 243 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 243 15 15, g32p_row07_traceSegment_013_0243_0015, g32p_row07_traceSegment_013_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 273 15 15, g32p_row07_traceSegment_013_0273_0015, g32p_row07_traceSegment_013_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_013 243 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 243 30 30, g32p_row07_traceSegment_013_0243_0030, g32p_row07_traceSegment_013_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 303 15 15, g32p_row07_traceSegment_013_0303_0015, g32p_row07_traceSegment_013_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 348 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 333 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 333 15 16, g32p_row07_traceSegment_013_0333_0015, g32p_row07_traceSegment_013_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 303 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 303 30 31, g32p_row07_traceSegment_013_0303_0030, g32p_row07_traceSegment_013_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_013 243 121 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 243 60 61, g32p_row07_traceSegment_013_0243_0060, g32p_row07_traceSegment_013_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 364 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 364 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 364 15 15, g32p_row07_traceSegment_013_0364_0015, g32p_row07_traceSegment_013_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 394 15 16, g32p_row07_traceSegment_013_0394_0015, g32p_row07_traceSegment_013_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 364 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 364 30 31, g32p_row07_traceSegment_013_0364_0030, g32p_row07_traceSegment_013_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 425 15 15, g32p_row07_traceSegment_013_0425_0015, g32p_row07_traceSegment_013_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 455 15 16, g32p_row07_traceSegment_013_0455_0015, g32p_row07_traceSegment_013_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 425 30 31, g32p_row07_traceSegment_013_0425_0030, g32p_row07_traceSegment_013_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_013 364 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 364 61 61, g32p_row07_traceSegment_013_0364_0061, g32p_row07_traceSegment_013_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_013 243 243 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 243 121 122, g32p_row07_traceSegment_013_0243_0121, g32p_row07_traceSegment_013_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_013 0 486 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 0 243 243, g32p_row07_traceSegment_013_0000_0243, g32p_row07_traceSegment_013_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 486 15 15, g32p_row07_traceSegment_013_0486_0015, g32p_row07_traceSegment_013_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 516 15 15, g32p_row07_traceSegment_013_0516_0015, g32p_row07_traceSegment_013_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_013 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 486 30 30, g32p_row07_traceSegment_013_0486_0030, g32p_row07_traceSegment_013_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 546 15 15, g32p_row07_traceSegment_013_0546_0015, g32p_row07_traceSegment_013_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 576 15 16, g32p_row07_traceSegment_013_0576_0015, g32p_row07_traceSegment_013_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 546 30 31, g32p_row07_traceSegment_013_0546_0030, g32p_row07_traceSegment_013_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_013 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 486 60 61, g32p_row07_traceSegment_013_0486_0060, g32p_row07_traceSegment_013_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 607 15 15, g32p_row07_traceSegment_013_0607_0015, g32p_row07_traceSegment_013_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 637 15 16, g32p_row07_traceSegment_013_0637_0015, g32p_row07_traceSegment_013_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 607 30 31, g32p_row07_traceSegment_013_0607_0030, g32p_row07_traceSegment_013_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 668 15 15, g32p_row07_traceSegment_013_0668_0015, g32p_row07_traceSegment_013_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 698 15 16, g32p_row07_traceSegment_013_0698_0015, g32p_row07_traceSegment_013_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 668 30 31, g32p_row07_traceSegment_013_0668_0030, g32p_row07_traceSegment_013_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_013 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 607 61 61, g32p_row07_traceSegment_013_0607_0061, g32p_row07_traceSegment_013_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_013 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 486 121 122, g32p_row07_traceSegment_013_0486_0121, g32p_row07_traceSegment_013_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 729 15 15, g32p_row07_traceSegment_013_0729_0015, g32p_row07_traceSegment_013_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 759 15 15, g32p_row07_traceSegment_013_0759_0015, g32p_row07_traceSegment_013_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_013 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 729 30 30, g32p_row07_traceSegment_013_0729_0030, g32p_row07_traceSegment_013_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 789 15 15, g32p_row07_traceSegment_013_0789_0015, g32p_row07_traceSegment_013_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 819 15 16, g32p_row07_traceSegment_013_0819_0015, g32p_row07_traceSegment_013_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 789 30 31, g32p_row07_traceSegment_013_0789_0030, g32p_row07_traceSegment_013_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_013 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 729 60 61, g32p_row07_traceSegment_013_0729_0060, g32p_row07_traceSegment_013_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 850 15 15, g32p_row07_traceSegment_013_0850_0015, g32p_row07_traceSegment_013_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 880 15 16, g32p_row07_traceSegment_013_0880_0015, g32p_row07_traceSegment_013_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 850 30 31, g32p_row07_traceSegment_013_0850_0030, g32p_row07_traceSegment_013_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 911 15 15, g32p_row07_traceSegment_013_0911_0015, g32p_row07_traceSegment_013_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 941 15 16, g32p_row07_traceSegment_013_0941_0015, g32p_row07_traceSegment_013_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 911 30 31, g32p_row07_traceSegment_013_0911_0030, g32p_row07_traceSegment_013_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_013 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 850 61 61, g32p_row07_traceSegment_013_0850_0061, g32p_row07_traceSegment_013_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_013 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 729 121 122, g32p_row07_traceSegment_013_0729_0121, g32p_row07_traceSegment_013_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_013 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 486 243 243, g32p_row07_traceSegment_013_0486_0243, g32p_row07_traceSegment_013_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_013 0 972 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 0 486 486, g32p_row07_traceSegment_013_0000_0486, g32p_row07_traceSegment_013_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 972 15 15, g32p_row07_traceSegment_013_0972_0015, g32p_row07_traceSegment_013_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1002 15 15, g32p_row07_traceSegment_013_1002_0015, g32p_row07_traceSegment_013_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_013 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 972 30 30, g32p_row07_traceSegment_013_0972_0030, g32p_row07_traceSegment_013_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1032 15 15, g32p_row07_traceSegment_013_1032_0015, g32p_row07_traceSegment_013_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1062 15 16, g32p_row07_traceSegment_013_1062_0015, g32p_row07_traceSegment_013_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1032 30 31, g32p_row07_traceSegment_013_1032_0030, g32p_row07_traceSegment_013_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_013 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 972 60 61, g32p_row07_traceSegment_013_0972_0060, g32p_row07_traceSegment_013_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1093 15 15, g32p_row07_traceSegment_013_1093_0015, g32p_row07_traceSegment_013_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1123 15 16, g32p_row07_traceSegment_013_1123_0015, g32p_row07_traceSegment_013_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1093 30 31, g32p_row07_traceSegment_013_1093_0030, g32p_row07_traceSegment_013_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1154 15 15, g32p_row07_traceSegment_013_1154_0015, g32p_row07_traceSegment_013_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1184 15 16, g32p_row07_traceSegment_013_1184_0015, g32p_row07_traceSegment_013_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1154 30 31, g32p_row07_traceSegment_013_1154_0030, g32p_row07_traceSegment_013_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_013 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1093 61 61, g32p_row07_traceSegment_013_1093_0061, g32p_row07_traceSegment_013_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_013 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 972 121 122, g32p_row07_traceSegment_013_0972_0121, g32p_row07_traceSegment_013_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1215 15 15, g32p_row07_traceSegment_013_1215_0015, g32p_row07_traceSegment_013_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1245 15 15, g32p_row07_traceSegment_013_1245_0015, g32p_row07_traceSegment_013_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_013 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1215 30 30, g32p_row07_traceSegment_013_1215_0030, g32p_row07_traceSegment_013_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1275 15 15, g32p_row07_traceSegment_013_1275_0015, g32p_row07_traceSegment_013_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1305 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1320 16 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1305 31 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1305 15 16, g32p_row07_traceSegment_013_1305_0015, g32p_row07_traceSegment_013_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1275 61 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1275 30 31, g32p_row07_traceSegment_013_1275_0030, g32p_row07_traceSegment_013_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_013 1215 121 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1215 60 61, g32p_row07_traceSegment_013_1215_0060, g32p_row07_traceSegment_013_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1336 15 15, g32p_row07_traceSegment_013_1336_0015, g32p_row07_traceSegment_013_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1366 15 16, g32p_row07_traceSegment_013_1366_0015, g32p_row07_traceSegment_013_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1336 30 31, g32p_row07_traceSegment_013_1336_0030, g32p_row07_traceSegment_013_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1397 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1412 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1397 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1397 15 15, g32p_row07_traceSegment_013_1397_0015, g32p_row07_traceSegment_013_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1427 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1427 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1427 15 16, g32p_row07_traceSegment_013_1427_0015, g32p_row07_traceSegment_013_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1397 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1397 30 31, g32p_row07_traceSegment_013_1397_0030, g32p_row07_traceSegment_013_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_013 1336 122 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1336 61 61, g32p_row07_traceSegment_013_1336_0061, g32p_row07_traceSegment_013_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_013 1215 243 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1215 121 122, g32p_row07_traceSegment_013_1215_0121, g32p_row07_traceSegment_013_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_013 972 486 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 972 243 243, g32p_row07_traceSegment_013_0972_0243, g32p_row07_traceSegment_013_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1458 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1458 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1458 15 15, g32p_row07_traceSegment_013_1458_0015, g32p_row07_traceSegment_013_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1488 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1503 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1488 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1488 15 15, g32p_row07_traceSegment_013_1488_0015, g32p_row07_traceSegment_013_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_013 1458 60 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1458 30 30, g32p_row07_traceSegment_013_1458_0030, g32p_row07_traceSegment_013_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1518 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1533 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1518 30 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1518 15 15, g32p_row07_traceSegment_013_1518_0015, g32p_row07_traceSegment_013_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1548 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1563 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1548 31 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1548 15 16, g32p_row07_traceSegment_013_1548_0015, g32p_row07_traceSegment_013_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1518 61 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1518 30 31, g32p_row07_traceSegment_013_1518_0030, g32p_row07_traceSegment_013_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_013 1458 121 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1458 60 61, g32p_row07_traceSegment_013_1458_0060, g32p_row07_traceSegment_013_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1579 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1594 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1579 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1579 15 15, g32p_row07_traceSegment_013_1579_0015, g32p_row07_traceSegment_013_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1609 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1624 16 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1609 31 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1609 15 16, g32p_row07_traceSegment_013_1609_0015, g32p_row07_traceSegment_013_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1579 61 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1579 30 31, g32p_row07_traceSegment_013_1579_0030, g32p_row07_traceSegment_013_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1640 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1655 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1640 30 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1640 15 15, g32p_row07_traceSegment_013_1640_0015, g32p_row07_traceSegment_013_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1670 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1685 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1670 31 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1670 15 16, g32p_row07_traceSegment_013_1670_0015, g32p_row07_traceSegment_013_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1640 61 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1640 30 31, g32p_row07_traceSegment_013_1640_0030, g32p_row07_traceSegment_013_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_013 1579 122 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1579 61 61, g32p_row07_traceSegment_013_1579_0061, g32p_row07_traceSegment_013_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_013 1458 243 = [0, 37] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1458 121 122, g32p_row07_traceSegment_013_1458_0121, g32p_row07_traceSegment_013_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1701 15 15, g32p_row07_traceSegment_013_1701_0015, g32p_row07_traceSegment_013_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1731 15 15, g32p_row07_traceSegment_013_1731_0015, g32p_row07_traceSegment_013_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_013 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1701 30 30, g32p_row07_traceSegment_013_1701_0030, g32p_row07_traceSegment_013_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1761 15 15, g32p_row07_traceSegment_013_1761_0015, g32p_row07_traceSegment_013_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1791 15 16, g32p_row07_traceSegment_013_1791_0015, g32p_row07_traceSegment_013_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1761 30 31, g32p_row07_traceSegment_013_1761_0030, g32p_row07_traceSegment_013_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_013 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1701 60 61, g32p_row07_traceSegment_013_1701_0060, g32p_row07_traceSegment_013_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1822 15 15, g32p_row07_traceSegment_013_1822_0015, g32p_row07_traceSegment_013_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1852 15 16, g32p_row07_traceSegment_013_1852_0015, g32p_row07_traceSegment_013_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1822 30 31, g32p_row07_traceSegment_013_1822_0030, g32p_row07_traceSegment_013_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_013 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1883 15 15, g32p_row07_traceSegment_013_1883_0015, g32p_row07_traceSegment_013_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_013 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_013 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_013_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_013 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1913 15 16, g32p_row07_traceSegment_013_1913_0015, g32p_row07_traceSegment_013_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_013 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1883 30 31, g32p_row07_traceSegment_013_1883_0030, g32p_row07_traceSegment_013_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_013 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1822 61 61, g32p_row07_traceSegment_013_1822_0061, g32p_row07_traceSegment_013_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_013 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1701 121 122, g32p_row07_traceSegment_013_1701_0121, g32p_row07_traceSegment_013_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_013_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_013 1458 486 = [0, 37] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 1458 243 243, g32p_row07_traceSegment_013_1458_0243, g32p_row07_traceSegment_013_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_013 972 972 = [0, 48] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 972 486 486, g32p_row07_traceSegment_013_0972_0486, g32p_row07_traceSegment_013_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_013_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_013 0 1944 = [0, 54] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_013 0 972 972, g32p_row07_traceSegment_013_0000_0972, g32p_row07_traceSegment_013_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 13 = [0, 54] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_013_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_014 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 14 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_014_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 0 15 15, g32p_row07_traceSegment_014_0000_0015, g32p_row07_traceSegment_014_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 30 15 15, g32p_row07_traceSegment_014_0030_0015, g32p_row07_traceSegment_014_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_014 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 0 30 30, g32p_row07_traceSegment_014_0000_0030, g32p_row07_traceSegment_014_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 75 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 60 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 60 15 15, g32p_row07_traceSegment_014_0060_0015, g32p_row07_traceSegment_014_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 90 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 105 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 90 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 90 15 16, g32p_row07_traceSegment_014_0090_0015, g32p_row07_traceSegment_014_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 60 61 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 60 30 31, g32p_row07_traceSegment_014_0060_0030, g32p_row07_traceSegment_014_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_014 0 121 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 0 60 61, g32p_row07_traceSegment_014_0000_0060, g32p_row07_traceSegment_014_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 121 15 = [0, 0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 136 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 121 30 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 121 15 15, g32p_row07_traceSegment_014_0121_0015, g32p_row07_traceSegment_014_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 151 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 151 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 151 15 16, g32p_row07_traceSegment_014_0151_0015, g32p_row07_traceSegment_014_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 121 61 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 121 30 31, g32p_row07_traceSegment_014_0121_0030, g32p_row07_traceSegment_014_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 182 15 15, g32p_row07_traceSegment_014_0182_0015, g32p_row07_traceSegment_014_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 212 15 16, g32p_row07_traceSegment_014_0212_0015, g32p_row07_traceSegment_014_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 182 30 31, g32p_row07_traceSegment_014_0182_0030, g32p_row07_traceSegment_014_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_014 121 122 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 121 61 61, g32p_row07_traceSegment_014_0121_0061, g32p_row07_traceSegment_014_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_014 0 243 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 0 121 122, g32p_row07_traceSegment_014_0000_0121, g32p_row07_traceSegment_014_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 243 15 15, g32p_row07_traceSegment_014_0243_0015, g32p_row07_traceSegment_014_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 273 15 15, g32p_row07_traceSegment_014_0273_0015, g32p_row07_traceSegment_014_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_014 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 243 30 30, g32p_row07_traceSegment_014_0243_0030, g32p_row07_traceSegment_014_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 303 15 15, g32p_row07_traceSegment_014_0303_0015, g32p_row07_traceSegment_014_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 333 15 16, g32p_row07_traceSegment_014_0333_0015, g32p_row07_traceSegment_014_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 303 30 31, g32p_row07_traceSegment_014_0303_0030, g32p_row07_traceSegment_014_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_014 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 243 60 61, g32p_row07_traceSegment_014_0243_0060, g32p_row07_traceSegment_014_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 364 15 15, g32p_row07_traceSegment_014_0364_0015, g32p_row07_traceSegment_014_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 394 15 16, g32p_row07_traceSegment_014_0394_0015, g32p_row07_traceSegment_014_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 364 30 31, g32p_row07_traceSegment_014_0364_0030, g32p_row07_traceSegment_014_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 425 15 15, g32p_row07_traceSegment_014_0425_0015, g32p_row07_traceSegment_014_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 455 15 16, g32p_row07_traceSegment_014_0455_0015, g32p_row07_traceSegment_014_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 425 30 31, g32p_row07_traceSegment_014_0425_0030, g32p_row07_traceSegment_014_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_014 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 364 61 61, g32p_row07_traceSegment_014_0364_0061, g32p_row07_traceSegment_014_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_014 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 243 121 122, g32p_row07_traceSegment_014_0243_0121, g32p_row07_traceSegment_014_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_014 0 486 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 0 243 243, g32p_row07_traceSegment_014_0000_0243, g32p_row07_traceSegment_014_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 486 15 15, g32p_row07_traceSegment_014_0486_0015, g32p_row07_traceSegment_014_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 516 15 15, g32p_row07_traceSegment_014_0516_0015, g32p_row07_traceSegment_014_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_014 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 486 30 30, g32p_row07_traceSegment_014_0486_0030, g32p_row07_traceSegment_014_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 546 15 15, g32p_row07_traceSegment_014_0546_0015, g32p_row07_traceSegment_014_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 576 15 16, g32p_row07_traceSegment_014_0576_0015, g32p_row07_traceSegment_014_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 546 30 31, g32p_row07_traceSegment_014_0546_0030, g32p_row07_traceSegment_014_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_014 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 486 60 61, g32p_row07_traceSegment_014_0486_0060, g32p_row07_traceSegment_014_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 607 15 15, g32p_row07_traceSegment_014_0607_0015, g32p_row07_traceSegment_014_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 637 15 16, g32p_row07_traceSegment_014_0637_0015, g32p_row07_traceSegment_014_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 607 30 31, g32p_row07_traceSegment_014_0607_0030, g32p_row07_traceSegment_014_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 668 15 15, g32p_row07_traceSegment_014_0668_0015, g32p_row07_traceSegment_014_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 698 15 16, g32p_row07_traceSegment_014_0698_0015, g32p_row07_traceSegment_014_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 668 30 31, g32p_row07_traceSegment_014_0668_0030, g32p_row07_traceSegment_014_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_014 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 607 61 61, g32p_row07_traceSegment_014_0607_0061, g32p_row07_traceSegment_014_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_014 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 486 121 122, g32p_row07_traceSegment_014_0486_0121, g32p_row07_traceSegment_014_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 729 15 15, g32p_row07_traceSegment_014_0729_0015, g32p_row07_traceSegment_014_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 774 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 759 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 759 15 15, g32p_row07_traceSegment_014_0759_0015, g32p_row07_traceSegment_014_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_014 729 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 729 30 30, g32p_row07_traceSegment_014_0729_0030, g32p_row07_traceSegment_014_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 789 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 804 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 789 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 789 15 15, g32p_row07_traceSegment_014_0789_0015, g32p_row07_traceSegment_014_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 819 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 834 16 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 819 31 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 819 15 16, g32p_row07_traceSegment_014_0819_0015, g32p_row07_traceSegment_014_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 789 61 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 789 30 31, g32p_row07_traceSegment_014_0789_0030, g32p_row07_traceSegment_014_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_014 729 121 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 729 60 61, g32p_row07_traceSegment_014_0729_0060, g32p_row07_traceSegment_014_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 850 15 = [0, 0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 865 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 850 30 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 850 15 15, g32p_row07_traceSegment_014_0850_0015, g32p_row07_traceSegment_014_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 880 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 895 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 880 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 880 15 16, g32p_row07_traceSegment_014_0880_0015, g32p_row07_traceSegment_014_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 850 61 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 850 30 31, g32p_row07_traceSegment_014_0850_0030, g32p_row07_traceSegment_014_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 911 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 926 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 911 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 911 15 15, g32p_row07_traceSegment_014_0911_0015, g32p_row07_traceSegment_014_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 941 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 956 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 941 31 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 941 15 16, g32p_row07_traceSegment_014_0941_0015, g32p_row07_traceSegment_014_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 911 61 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 911 30 31, g32p_row07_traceSegment_014_0911_0030, g32p_row07_traceSegment_014_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_014 850 122 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 850 61 61, g32p_row07_traceSegment_014_0850_0061, g32p_row07_traceSegment_014_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_014 729 243 = [0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 729 121 122, g32p_row07_traceSegment_014_0729_0121, g32p_row07_traceSegment_014_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_014 486 486 = [0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 486 243 243, g32p_row07_traceSegment_014_0486_0243, g32p_row07_traceSegment_014_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_014 0 972 = [0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 0 486 486, g32p_row07_traceSegment_014_0000_0486, g32p_row07_traceSegment_014_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 987 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 972 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 972 15 15, g32p_row07_traceSegment_014_0972_0015, g32p_row07_traceSegment_014_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1017 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1002 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1002 15 15, g32p_row07_traceSegment_014_1002_0015, g32p_row07_traceSegment_014_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_014 972 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 972 30 30, g32p_row07_traceSegment_014_0972_0030, g32p_row07_traceSegment_014_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1032 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1032 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1032 15 15, g32p_row07_traceSegment_014_1032_0015, g32p_row07_traceSegment_014_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1077 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1062 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1062 15 16, g32p_row07_traceSegment_014_1062_0015, g32p_row07_traceSegment_014_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1032 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1032 30 31, g32p_row07_traceSegment_014_1032_0030, g32p_row07_traceSegment_014_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_014 972 121 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 972 60 61, g32p_row07_traceSegment_014_0972_0060, g32p_row07_traceSegment_014_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1093 15 15, g32p_row07_traceSegment_014_1093_0015, g32p_row07_traceSegment_014_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1123 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1138 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1123 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1123 15 16, g32p_row07_traceSegment_014_1123_0015, g32p_row07_traceSegment_014_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1093 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1093 30 31, g32p_row07_traceSegment_014_1093_0030, g32p_row07_traceSegment_014_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1154 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1154 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1154 15 15, g32p_row07_traceSegment_014_1154_0015, g32p_row07_traceSegment_014_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1199 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1184 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1184 15 16, g32p_row07_traceSegment_014_1184_0015, g32p_row07_traceSegment_014_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1154 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1154 30 31, g32p_row07_traceSegment_014_1154_0030, g32p_row07_traceSegment_014_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_014 1093 122 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1093 61 61, g32p_row07_traceSegment_014_1093_0061, g32p_row07_traceSegment_014_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_014 972 243 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 972 121 122, g32p_row07_traceSegment_014_0972_0121, g32p_row07_traceSegment_014_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1215 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1230 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1215 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1215 15 15, g32p_row07_traceSegment_014_1215_0015, g32p_row07_traceSegment_014_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1245 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1245 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1245 15 15, g32p_row07_traceSegment_014_1245_0015, g32p_row07_traceSegment_014_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_014 1215 60 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1215 30 30, g32p_row07_traceSegment_014_1215_0030, g32p_row07_traceSegment_014_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1275 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1275 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1275 15 15, g32p_row07_traceSegment_014_1275_0015, g32p_row07_traceSegment_014_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1305 15 16, g32p_row07_traceSegment_014_1305_0015, g32p_row07_traceSegment_014_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1275 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1275 30 31, g32p_row07_traceSegment_014_1275_0030, g32p_row07_traceSegment_014_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_014 1215 121 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1215 60 61, g32p_row07_traceSegment_014_1215_0060, g32p_row07_traceSegment_014_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1336 15 15, g32p_row07_traceSegment_014_1336_0015, g32p_row07_traceSegment_014_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1366 15 16, g32p_row07_traceSegment_014_1366_0015, g32p_row07_traceSegment_014_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1336 30 31, g32p_row07_traceSegment_014_1336_0030, g32p_row07_traceSegment_014_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1397 15 15, g32p_row07_traceSegment_014_1397_0015, g32p_row07_traceSegment_014_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1427 15 16, g32p_row07_traceSegment_014_1427_0015, g32p_row07_traceSegment_014_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1397 30 31, g32p_row07_traceSegment_014_1397_0030, g32p_row07_traceSegment_014_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_014 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1336 61 61, g32p_row07_traceSegment_014_1336_0061, g32p_row07_traceSegment_014_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_014 1215 243 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1215 121 122, g32p_row07_traceSegment_014_1215_0121, g32p_row07_traceSegment_014_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_014 972 486 = [0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 972 243 243, g32p_row07_traceSegment_014_0972_0243, g32p_row07_traceSegment_014_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1458 15 15, g32p_row07_traceSegment_014_1458_0015, g32p_row07_traceSegment_014_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1488 15 15, g32p_row07_traceSegment_014_1488_0015, g32p_row07_traceSegment_014_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_014 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1458 30 30, g32p_row07_traceSegment_014_1458_0030, g32p_row07_traceSegment_014_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1518 15 15, g32p_row07_traceSegment_014_1518_0015, g32p_row07_traceSegment_014_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1548 15 16, g32p_row07_traceSegment_014_1548_0015, g32p_row07_traceSegment_014_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1518 30 31, g32p_row07_traceSegment_014_1518_0030, g32p_row07_traceSegment_014_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_014 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1458 60 61, g32p_row07_traceSegment_014_1458_0060, g32p_row07_traceSegment_014_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1579 15 15, g32p_row07_traceSegment_014_1579_0015, g32p_row07_traceSegment_014_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1609 15 16, g32p_row07_traceSegment_014_1609_0015, g32p_row07_traceSegment_014_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1579 30 31, g32p_row07_traceSegment_014_1579_0030, g32p_row07_traceSegment_014_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1640 15 15, g32p_row07_traceSegment_014_1640_0015, g32p_row07_traceSegment_014_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1670 15 16, g32p_row07_traceSegment_014_1670_0015, g32p_row07_traceSegment_014_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1640 30 31, g32p_row07_traceSegment_014_1640_0030, g32p_row07_traceSegment_014_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_014 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1579 61 61, g32p_row07_traceSegment_014_1579_0061, g32p_row07_traceSegment_014_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_014 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1458 121 122, g32p_row07_traceSegment_014_1458_0121, g32p_row07_traceSegment_014_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1701 15 15, g32p_row07_traceSegment_014_1701_0015, g32p_row07_traceSegment_014_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1731 15 15, g32p_row07_traceSegment_014_1731_0015, g32p_row07_traceSegment_014_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_014 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1701 30 30, g32p_row07_traceSegment_014_1701_0030, g32p_row07_traceSegment_014_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1761 15 15, g32p_row07_traceSegment_014_1761_0015, g32p_row07_traceSegment_014_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1791 15 16, g32p_row07_traceSegment_014_1791_0015, g32p_row07_traceSegment_014_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1761 30 31, g32p_row07_traceSegment_014_1761_0030, g32p_row07_traceSegment_014_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_014 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1701 60 61, g32p_row07_traceSegment_014_1701_0060, g32p_row07_traceSegment_014_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1822 15 15, g32p_row07_traceSegment_014_1822_0015, g32p_row07_traceSegment_014_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1852 15 16, g32p_row07_traceSegment_014_1852_0015, g32p_row07_traceSegment_014_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1822 30 31, g32p_row07_traceSegment_014_1822_0030, g32p_row07_traceSegment_014_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_014 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1883 15 15, g32p_row07_traceSegment_014_1883_0015, g32p_row07_traceSegment_014_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_014 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_014 1928 16 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_014_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_014 1913 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1913 15 16, g32p_row07_traceSegment_014_1913_0015, g32p_row07_traceSegment_014_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_014 1883 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1883 30 31, g32p_row07_traceSegment_014_1883_0030, g32p_row07_traceSegment_014_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_014 1822 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1822 61 61, g32p_row07_traceSegment_014_1822_0061, g32p_row07_traceSegment_014_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_014 1701 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1701 121 122, g32p_row07_traceSegment_014_1701_0121, g32p_row07_traceSegment_014_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_014_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_014 1458 486 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 1458 243 243, g32p_row07_traceSegment_014_1458_0243, g32p_row07_traceSegment_014_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_014 972 972 = [0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 972 486 486, g32p_row07_traceSegment_014_0972_0486, g32p_row07_traceSegment_014_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_014_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_014 0 1944 = [0, 0, 72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_014 0 972 972, g32p_row07_traceSegment_014_0000_0972, g32p_row07_traceSegment_014_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_014 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 14 = [0, 0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_014_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_021 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 21 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_021_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 15 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 0 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 0 15 15, g32p_row07_traceSegment_021_0000_0015, g32p_row07_traceSegment_021_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 30 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 45 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 30 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 30 15 15, g32p_row07_traceSegment_021_0030_0015, g32p_row07_traceSegment_021_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_021 0 60 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 0 30 30, g32p_row07_traceSegment_021_0000_0030, g32p_row07_traceSegment_021_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 60 15 15, g32p_row07_traceSegment_021_0060_0015, g32p_row07_traceSegment_021_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 90 15 16, g32p_row07_traceSegment_021_0090_0015, g32p_row07_traceSegment_021_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 60 30 31, g32p_row07_traceSegment_021_0060_0030, g32p_row07_traceSegment_021_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_021 0 121 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 0 60 61, g32p_row07_traceSegment_021_0000_0060, g32p_row07_traceSegment_021_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 121 15 15, g32p_row07_traceSegment_021_0121_0015, g32p_row07_traceSegment_021_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 151 15 16, g32p_row07_traceSegment_021_0151_0015, g32p_row07_traceSegment_021_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 121 30 31, g32p_row07_traceSegment_021_0121_0030, g32p_row07_traceSegment_021_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 182 15 15, g32p_row07_traceSegment_021_0182_0015, g32p_row07_traceSegment_021_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 212 15 16, g32p_row07_traceSegment_021_0212_0015, g32p_row07_traceSegment_021_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 182 30 31, g32p_row07_traceSegment_021_0182_0030, g32p_row07_traceSegment_021_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_021 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 121 61 61, g32p_row07_traceSegment_021_0121_0061, g32p_row07_traceSegment_021_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_021 0 243 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 0 121 122, g32p_row07_traceSegment_021_0000_0121, g32p_row07_traceSegment_021_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 243 15 15, g32p_row07_traceSegment_021_0243_0015, g32p_row07_traceSegment_021_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 273 15 15, g32p_row07_traceSegment_021_0273_0015, g32p_row07_traceSegment_021_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_021 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 243 30 30, g32p_row07_traceSegment_021_0243_0030, g32p_row07_traceSegment_021_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 303 15 15, g32p_row07_traceSegment_021_0303_0015, g32p_row07_traceSegment_021_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 333 15 16, g32p_row07_traceSegment_021_0333_0015, g32p_row07_traceSegment_021_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 303 30 31, g32p_row07_traceSegment_021_0303_0030, g32p_row07_traceSegment_021_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_021 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 243 60 61, g32p_row07_traceSegment_021_0243_0060, g32p_row07_traceSegment_021_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 379 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 364 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 364 15 15, g32p_row07_traceSegment_021_0364_0015, g32p_row07_traceSegment_021_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 394 15 16, g32p_row07_traceSegment_021_0394_0015, g32p_row07_traceSegment_021_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 364 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 364 30 31, g32p_row07_traceSegment_021_0364_0030, g32p_row07_traceSegment_021_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 425 15 15, g32p_row07_traceSegment_021_0425_0015, g32p_row07_traceSegment_021_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 455 15 16, g32p_row07_traceSegment_021_0455_0015, g32p_row07_traceSegment_021_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 425 30 31, g32p_row07_traceSegment_021_0425_0030, g32p_row07_traceSegment_021_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_021 364 122 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 364 61 61, g32p_row07_traceSegment_021_0364_0061, g32p_row07_traceSegment_021_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_021 243 243 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 243 121 122, g32p_row07_traceSegment_021_0243_0121, g32p_row07_traceSegment_021_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_021 0 486 = [13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 0 243 243, g32p_row07_traceSegment_021_0000_0243, g32p_row07_traceSegment_021_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 486 15 15, g32p_row07_traceSegment_021_0486_0015, g32p_row07_traceSegment_021_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 516 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 531 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 516 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 516 15 15, g32p_row07_traceSegment_021_0516_0015, g32p_row07_traceSegment_021_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_021 486 60 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 486 30 30, g32p_row07_traceSegment_021_0486_0030, g32p_row07_traceSegment_021_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 546 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 561 15 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 546 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 546 15 15, g32p_row07_traceSegment_021_0546_0015, g32p_row07_traceSegment_021_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 576 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 591 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 576 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 576 15 16, g32p_row07_traceSegment_021_0576_0015, g32p_row07_traceSegment_021_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 546 61 = [10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 546 30 31, g32p_row07_traceSegment_021_0546_0030, g32p_row07_traceSegment_021_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_021 486 121 = [13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 486 60 61, g32p_row07_traceSegment_021_0486_0060, g32p_row07_traceSegment_021_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 622 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 607 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 607 15 15, g32p_row07_traceSegment_021_0607_0015, g32p_row07_traceSegment_021_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 637 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 652 16 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 637 31 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 637 15 16, g32p_row07_traceSegment_021_0637_0015, g32p_row07_traceSegment_021_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 607 61 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 607 30 31, g32p_row07_traceSegment_021_0607_0030, g32p_row07_traceSegment_021_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 668 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 683 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 668 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 668 15 15, g32p_row07_traceSegment_021_0668_0015, g32p_row07_traceSegment_021_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 698 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 713 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 698 31 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 698 15 16, g32p_row07_traceSegment_021_0698_0015, g32p_row07_traceSegment_021_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 668 61 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 668 30 31, g32p_row07_traceSegment_021_0668_0030, g32p_row07_traceSegment_021_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_021 607 122 = [16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 607 61 61, g32p_row07_traceSegment_021_0607_0061, g32p_row07_traceSegment_021_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_021 486 243 = [29] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 486 121 122, g32p_row07_traceSegment_021_0486_0121, g32p_row07_traceSegment_021_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 729 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 744 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 729 30 = [12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 729 15 15, g32p_row07_traceSegment_021_0729_0015, g32p_row07_traceSegment_021_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 759 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 759 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 759 15 15, g32p_row07_traceSegment_021_0759_0015, g32p_row07_traceSegment_021_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_021 729 60 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 729 30 30, g32p_row07_traceSegment_021_0729_0030, g32p_row07_traceSegment_021_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 789 15 15, g32p_row07_traceSegment_021_0789_0015, g32p_row07_traceSegment_021_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 819 15 16, g32p_row07_traceSegment_021_0819_0015, g32p_row07_traceSegment_021_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 789 30 31, g32p_row07_traceSegment_021_0789_0030, g32p_row07_traceSegment_021_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_021 729 121 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 729 60 61, g32p_row07_traceSegment_021_0729_0060, g32p_row07_traceSegment_021_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 850 15 15, g32p_row07_traceSegment_021_0850_0015, g32p_row07_traceSegment_021_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 880 15 16, g32p_row07_traceSegment_021_0880_0015, g32p_row07_traceSegment_021_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 850 30 31, g32p_row07_traceSegment_021_0850_0030, g32p_row07_traceSegment_021_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 911 15 15, g32p_row07_traceSegment_021_0911_0015, g32p_row07_traceSegment_021_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 941 15 16, g32p_row07_traceSegment_021_0941_0015, g32p_row07_traceSegment_021_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 911 30 31, g32p_row07_traceSegment_021_0911_0030, g32p_row07_traceSegment_021_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_021 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 850 61 61, g32p_row07_traceSegment_021_0850_0061, g32p_row07_traceSegment_021_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_021 729 243 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 729 121 122, g32p_row07_traceSegment_021_0729_0121, g32p_row07_traceSegment_021_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_021 486 486 = [47] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 486 243 243, g32p_row07_traceSegment_021_0486_0243, g32p_row07_traceSegment_021_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_021 0 972 = [60] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 0 486 486, g32p_row07_traceSegment_021_0000_0486, g32p_row07_traceSegment_021_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 972 15 15, g32p_row07_traceSegment_021_0972_0015, g32p_row07_traceSegment_021_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1002 15 15, g32p_row07_traceSegment_021_1002_0015, g32p_row07_traceSegment_021_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_021 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 972 30 30, g32p_row07_traceSegment_021_0972_0030, g32p_row07_traceSegment_021_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1032 15 15, g32p_row07_traceSegment_021_1032_0015, g32p_row07_traceSegment_021_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1062 15 16, g32p_row07_traceSegment_021_1062_0015, g32p_row07_traceSegment_021_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1032 30 31, g32p_row07_traceSegment_021_1032_0030, g32p_row07_traceSegment_021_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_021 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 972 60 61, g32p_row07_traceSegment_021_0972_0060, g32p_row07_traceSegment_021_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1093 15 15, g32p_row07_traceSegment_021_1093_0015, g32p_row07_traceSegment_021_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1123 15 16, g32p_row07_traceSegment_021_1123_0015, g32p_row07_traceSegment_021_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1093 30 31, g32p_row07_traceSegment_021_1093_0030, g32p_row07_traceSegment_021_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1154 15 15, g32p_row07_traceSegment_021_1154_0015, g32p_row07_traceSegment_021_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1184 15 16, g32p_row07_traceSegment_021_1184_0015, g32p_row07_traceSegment_021_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1154 30 31, g32p_row07_traceSegment_021_1154_0030, g32p_row07_traceSegment_021_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_021 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1093 61 61, g32p_row07_traceSegment_021_1093_0061, g32p_row07_traceSegment_021_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_021 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 972 121 122, g32p_row07_traceSegment_021_0972_0121, g32p_row07_traceSegment_021_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1215 15 15, g32p_row07_traceSegment_021_1215_0015, g32p_row07_traceSegment_021_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1245 15 15, g32p_row07_traceSegment_021_1245_0015, g32p_row07_traceSegment_021_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_021 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1215 30 30, g32p_row07_traceSegment_021_1215_0030, g32p_row07_traceSegment_021_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1275 15 15, g32p_row07_traceSegment_021_1275_0015, g32p_row07_traceSegment_021_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1305 15 16, g32p_row07_traceSegment_021_1305_0015, g32p_row07_traceSegment_021_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1275 30 31, g32p_row07_traceSegment_021_1275_0030, g32p_row07_traceSegment_021_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_021 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1215 60 61, g32p_row07_traceSegment_021_1215_0060, g32p_row07_traceSegment_021_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1336 15 15, g32p_row07_traceSegment_021_1336_0015, g32p_row07_traceSegment_021_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1366 15 16, g32p_row07_traceSegment_021_1366_0015, g32p_row07_traceSegment_021_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1336 30 31, g32p_row07_traceSegment_021_1336_0030, g32p_row07_traceSegment_021_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1397 15 15, g32p_row07_traceSegment_021_1397_0015, g32p_row07_traceSegment_021_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1427 15 16, g32p_row07_traceSegment_021_1427_0015, g32p_row07_traceSegment_021_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1397 30 31, g32p_row07_traceSegment_021_1397_0030, g32p_row07_traceSegment_021_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_021 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1336 61 61, g32p_row07_traceSegment_021_1336_0061, g32p_row07_traceSegment_021_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_021 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1215 121 122, g32p_row07_traceSegment_021_1215_0121, g32p_row07_traceSegment_021_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_021 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 972 243 243, g32p_row07_traceSegment_021_0972_0243, g32p_row07_traceSegment_021_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1458 15 15, g32p_row07_traceSegment_021_1458_0015, g32p_row07_traceSegment_021_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1488 15 15, g32p_row07_traceSegment_021_1488_0015, g32p_row07_traceSegment_021_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_021 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1458 30 30, g32p_row07_traceSegment_021_1458_0030, g32p_row07_traceSegment_021_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1518 15 15, g32p_row07_traceSegment_021_1518_0015, g32p_row07_traceSegment_021_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1548 15 16, g32p_row07_traceSegment_021_1548_0015, g32p_row07_traceSegment_021_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1518 30 31, g32p_row07_traceSegment_021_1518_0030, g32p_row07_traceSegment_021_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_021 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1458 60 61, g32p_row07_traceSegment_021_1458_0060, g32p_row07_traceSegment_021_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1579 15 15, g32p_row07_traceSegment_021_1579_0015, g32p_row07_traceSegment_021_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1609 15 16, g32p_row07_traceSegment_021_1609_0015, g32p_row07_traceSegment_021_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1579 30 31, g32p_row07_traceSegment_021_1579_0030, g32p_row07_traceSegment_021_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1640 15 15, g32p_row07_traceSegment_021_1640_0015, g32p_row07_traceSegment_021_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1670 15 16, g32p_row07_traceSegment_021_1670_0015, g32p_row07_traceSegment_021_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1640 30 31, g32p_row07_traceSegment_021_1640_0030, g32p_row07_traceSegment_021_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_021 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1579 61 61, g32p_row07_traceSegment_021_1579_0061, g32p_row07_traceSegment_021_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_021 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1458 121 122, g32p_row07_traceSegment_021_1458_0121, g32p_row07_traceSegment_021_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1701 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1716 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1701 30 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1701 15 15, g32p_row07_traceSegment_021_1701_0015, g32p_row07_traceSegment_021_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1746 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1731 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1731 15 15, g32p_row07_traceSegment_021_1731_0015, g32p_row07_traceSegment_021_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_021 1701 60 = [11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1701 30 30, g32p_row07_traceSegment_021_1701_0030, g32p_row07_traceSegment_021_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1761 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1776 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1761 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1761 15 15, g32p_row07_traceSegment_021_1761_0015, g32p_row07_traceSegment_021_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1791 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1806 16 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1791 31 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1791 15 16, g32p_row07_traceSegment_021_1791_0015, g32p_row07_traceSegment_021_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1761 61 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1761 30 31, g32p_row07_traceSegment_021_1761_0030, g32p_row07_traceSegment_021_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_021 1701 121 = [20] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1701 60 61, g32p_row07_traceSegment_021_1701_0060, g32p_row07_traceSegment_021_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1822 15 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1837 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1822 30 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1822 15 15, g32p_row07_traceSegment_021_1822_0015, g32p_row07_traceSegment_021_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1852 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1867 16 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1852 31 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1852 15 16, g32p_row07_traceSegment_021_1852_0015, g32p_row07_traceSegment_021_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1822 61 = [15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1822 30 31, g32p_row07_traceSegment_021_1822_0030, g32p_row07_traceSegment_021_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1883 15 = [7] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1898 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_021 1883 30 = [11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1883 15 15, g32p_row07_traceSegment_021_1883_0015, g32p_row07_traceSegment_021_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_021 1913 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_021 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_021_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_021 1913 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1913 15 16, g32p_row07_traceSegment_021_1913_0015, g32p_row07_traceSegment_021_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_021 1883 61 = [13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1883 30 31, g32p_row07_traceSegment_021_1883_0030, g32p_row07_traceSegment_021_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_021 1822 122 = [28] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1822 61 61, g32p_row07_traceSegment_021_1822_0061, g32p_row07_traceSegment_021_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_021 1701 243 = [48] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1701 121 122, g32p_row07_traceSegment_021_1701_0121, g32p_row07_traceSegment_021_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_021_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_021 1458 486 = [48] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 1458 243 243, g32p_row07_traceSegment_021_1458_0243, g32p_row07_traceSegment_021_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_021 972 972 = [48] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 972 486 486, g32p_row07_traceSegment_021_0972_0486, g32p_row07_traceSegment_021_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_021_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_021 0 1944 = [108] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_021 0 972 972, g32p_row07_traceSegment_021_0000_0972, g32p_row07_traceSegment_021_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_021 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 21 = [108] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_021_0000_1944

end HodgeLean.Foundations.Program

end
end
