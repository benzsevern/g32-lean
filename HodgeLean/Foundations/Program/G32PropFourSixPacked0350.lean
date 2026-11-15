import HodgeLean.Foundations.Program.G32PropFourSixPacked0347
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0349

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_039 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 39 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_039_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 0 15 15, g32p_row07_traceSegment_039_0000_0015, g32p_row07_traceSegment_039_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 30 15 15, g32p_row07_traceSegment_039_0030_0015, g32p_row07_traceSegment_039_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_039 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 0 30 30, g32p_row07_traceSegment_039_0000_0030, g32p_row07_traceSegment_039_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 60 15 15, g32p_row07_traceSegment_039_0060_0015, g32p_row07_traceSegment_039_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 90 15 16, g32p_row07_traceSegment_039_0090_0015, g32p_row07_traceSegment_039_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 60 30 31, g32p_row07_traceSegment_039_0060_0030, g32p_row07_traceSegment_039_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_039 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 0 60 61, g32p_row07_traceSegment_039_0000_0060, g32p_row07_traceSegment_039_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 121 15 15, g32p_row07_traceSegment_039_0121_0015, g32p_row07_traceSegment_039_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 151 15 16, g32p_row07_traceSegment_039_0151_0015, g32p_row07_traceSegment_039_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 121 30 31, g32p_row07_traceSegment_039_0121_0030, g32p_row07_traceSegment_039_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 182 15 15, g32p_row07_traceSegment_039_0182_0015, g32p_row07_traceSegment_039_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 212 15 16, g32p_row07_traceSegment_039_0212_0015, g32p_row07_traceSegment_039_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 182 30 31, g32p_row07_traceSegment_039_0182_0030, g32p_row07_traceSegment_039_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_039 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 121 61 61, g32p_row07_traceSegment_039_0121_0061, g32p_row07_traceSegment_039_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_039 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 0 121 122, g32p_row07_traceSegment_039_0000_0121, g32p_row07_traceSegment_039_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 243 15 15, g32p_row07_traceSegment_039_0243_0015, g32p_row07_traceSegment_039_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 273 15 15, g32p_row07_traceSegment_039_0273_0015, g32p_row07_traceSegment_039_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_039 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 243 30 30, g32p_row07_traceSegment_039_0243_0030, g32p_row07_traceSegment_039_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 303 15 15, g32p_row07_traceSegment_039_0303_0015, g32p_row07_traceSegment_039_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 333 15 16, g32p_row07_traceSegment_039_0333_0015, g32p_row07_traceSegment_039_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 303 30 31, g32p_row07_traceSegment_039_0303_0030, g32p_row07_traceSegment_039_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_039 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 243 60 61, g32p_row07_traceSegment_039_0243_0060, g32p_row07_traceSegment_039_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 364 15 15, g32p_row07_traceSegment_039_0364_0015, g32p_row07_traceSegment_039_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 394 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 394 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 394 15 16, g32p_row07_traceSegment_039_0394_0015, g32p_row07_traceSegment_039_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 364 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 364 30 31, g32p_row07_traceSegment_039_0364_0030, g32p_row07_traceSegment_039_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 425 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 440 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 425 30 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 425 15 15, g32p_row07_traceSegment_039_0425_0015, g32p_row07_traceSegment_039_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 455 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 470 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 455 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 455 15 16, g32p_row07_traceSegment_039_0455_0015, g32p_row07_traceSegment_039_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 425 61 = [12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 425 30 31, g32p_row07_traceSegment_039_0425_0030, g32p_row07_traceSegment_039_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_039 364 122 = [14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 364 61 61, g32p_row07_traceSegment_039_0364_0061, g32p_row07_traceSegment_039_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_039 243 243 = [14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 243 121 122, g32p_row07_traceSegment_039_0243_0121, g32p_row07_traceSegment_039_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_039 0 486 = [14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 0 243 243, g32p_row07_traceSegment_039_0000_0243, g32p_row07_traceSegment_039_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 486 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 501 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 486 30 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 486 15 15, g32p_row07_traceSegment_039_0486_0015, g32p_row07_traceSegment_039_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 516 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 531 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 516 30 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 516 15 15, g32p_row07_traceSegment_039_0516_0015, g32p_row07_traceSegment_039_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_039 486 60 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 486 30 30, g32p_row07_traceSegment_039_0486_0030, g32p_row07_traceSegment_039_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 546 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 546 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 546 15 15, g32p_row07_traceSegment_039_0546_0015, g32p_row07_traceSegment_039_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 576 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 591 16 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 576 31 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 576 15 16, g32p_row07_traceSegment_039_0576_0015, g32p_row07_traceSegment_039_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 546 61 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 546 30 31, g32p_row07_traceSegment_039_0546_0030, g32p_row07_traceSegment_039_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_039 486 121 = [27] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 486 60 61, g32p_row07_traceSegment_039_0486_0060, g32p_row07_traceSegment_039_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 607 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 607 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 607 15 15, g32p_row07_traceSegment_039_0607_0015, g32p_row07_traceSegment_039_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 637 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 652 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 637 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 637 15 16, g32p_row07_traceSegment_039_0637_0015, g32p_row07_traceSegment_039_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 607 61 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 607 30 31, g32p_row07_traceSegment_039_0607_0030, g32p_row07_traceSegment_039_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 668 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 683 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 668 30 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 668 15 15, g32p_row07_traceSegment_039_0668_0015, g32p_row07_traceSegment_039_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 698 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 713 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 698 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 698 15 16, g32p_row07_traceSegment_039_0698_0015, g32p_row07_traceSegment_039_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 668 61 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 668 30 31, g32p_row07_traceSegment_039_0668_0030, g32p_row07_traceSegment_039_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_039 607 122 = [15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 607 61 61, g32p_row07_traceSegment_039_0607_0061, g32p_row07_traceSegment_039_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_039 486 243 = [42] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 486 121 122, g32p_row07_traceSegment_039_0486_0121, g32p_row07_traceSegment_039_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 744 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 729 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 729 15 15, g32p_row07_traceSegment_039_0729_0015, g32p_row07_traceSegment_039_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 759 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 759 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 759 15 15, g32p_row07_traceSegment_039_0759_0015, g32p_row07_traceSegment_039_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_039 729 60 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 729 30 30, g32p_row07_traceSegment_039_0729_0030, g32p_row07_traceSegment_039_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 789 15 15, g32p_row07_traceSegment_039_0789_0015, g32p_row07_traceSegment_039_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 819 15 16, g32p_row07_traceSegment_039_0819_0015, g32p_row07_traceSegment_039_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 789 30 31, g32p_row07_traceSegment_039_0789_0030, g32p_row07_traceSegment_039_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_039 729 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 729 60 61, g32p_row07_traceSegment_039_0729_0060, g32p_row07_traceSegment_039_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 850 15 15, g32p_row07_traceSegment_039_0850_0015, g32p_row07_traceSegment_039_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 880 15 16, g32p_row07_traceSegment_039_0880_0015, g32p_row07_traceSegment_039_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 850 30 31, g32p_row07_traceSegment_039_0850_0030, g32p_row07_traceSegment_039_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 911 15 15, g32p_row07_traceSegment_039_0911_0015, g32p_row07_traceSegment_039_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 941 15 16, g32p_row07_traceSegment_039_0941_0015, g32p_row07_traceSegment_039_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 911 30 31, g32p_row07_traceSegment_039_0911_0030, g32p_row07_traceSegment_039_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_039 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 850 61 61, g32p_row07_traceSegment_039_0850_0061, g32p_row07_traceSegment_039_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_039 729 243 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 729 121 122, g32p_row07_traceSegment_039_0729_0121, g32p_row07_traceSegment_039_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_039 486 486 = [45] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 486 243 243, g32p_row07_traceSegment_039_0486_0243, g32p_row07_traceSegment_039_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_039 0 972 = [59] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 0 486 486, g32p_row07_traceSegment_039_0000_0486, g32p_row07_traceSegment_039_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 972 15 15, g32p_row07_traceSegment_039_0972_0015, g32p_row07_traceSegment_039_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1002 15 15, g32p_row07_traceSegment_039_1002_0015, g32p_row07_traceSegment_039_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_039 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 972 30 30, g32p_row07_traceSegment_039_0972_0030, g32p_row07_traceSegment_039_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1032 15 15, g32p_row07_traceSegment_039_1032_0015, g32p_row07_traceSegment_039_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1062 15 16, g32p_row07_traceSegment_039_1062_0015, g32p_row07_traceSegment_039_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1032 30 31, g32p_row07_traceSegment_039_1032_0030, g32p_row07_traceSegment_039_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_039 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 972 60 61, g32p_row07_traceSegment_039_0972_0060, g32p_row07_traceSegment_039_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1093 15 15, g32p_row07_traceSegment_039_1093_0015, g32p_row07_traceSegment_039_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1123 15 16, g32p_row07_traceSegment_039_1123_0015, g32p_row07_traceSegment_039_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1093 30 31, g32p_row07_traceSegment_039_1093_0030, g32p_row07_traceSegment_039_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1154 15 15, g32p_row07_traceSegment_039_1154_0015, g32p_row07_traceSegment_039_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1184 15 16, g32p_row07_traceSegment_039_1184_0015, g32p_row07_traceSegment_039_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1154 30 31, g32p_row07_traceSegment_039_1154_0030, g32p_row07_traceSegment_039_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_039 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1093 61 61, g32p_row07_traceSegment_039_1093_0061, g32p_row07_traceSegment_039_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_039 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 972 121 122, g32p_row07_traceSegment_039_0972_0121, g32p_row07_traceSegment_039_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1215 15 15, g32p_row07_traceSegment_039_1215_0015, g32p_row07_traceSegment_039_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1245 15 15, g32p_row07_traceSegment_039_1245_0015, g32p_row07_traceSegment_039_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_039 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1215 30 30, g32p_row07_traceSegment_039_1215_0030, g32p_row07_traceSegment_039_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1275 15 15, g32p_row07_traceSegment_039_1275_0015, g32p_row07_traceSegment_039_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1305 15 16, g32p_row07_traceSegment_039_1305_0015, g32p_row07_traceSegment_039_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1275 30 31, g32p_row07_traceSegment_039_1275_0030, g32p_row07_traceSegment_039_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_039 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1215 60 61, g32p_row07_traceSegment_039_1215_0060, g32p_row07_traceSegment_039_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1336 15 15, g32p_row07_traceSegment_039_1336_0015, g32p_row07_traceSegment_039_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1366 15 16, g32p_row07_traceSegment_039_1366_0015, g32p_row07_traceSegment_039_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1336 30 31, g32p_row07_traceSegment_039_1336_0030, g32p_row07_traceSegment_039_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1397 15 15, g32p_row07_traceSegment_039_1397_0015, g32p_row07_traceSegment_039_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1427 15 16, g32p_row07_traceSegment_039_1427_0015, g32p_row07_traceSegment_039_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1397 30 31, g32p_row07_traceSegment_039_1397_0030, g32p_row07_traceSegment_039_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_039 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1336 61 61, g32p_row07_traceSegment_039_1336_0061, g32p_row07_traceSegment_039_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_039 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1215 121 122, g32p_row07_traceSegment_039_1215_0121, g32p_row07_traceSegment_039_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_039 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 972 243 243, g32p_row07_traceSegment_039_0972_0243, g32p_row07_traceSegment_039_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1458 15 15, g32p_row07_traceSegment_039_1458_0015, g32p_row07_traceSegment_039_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1488 15 15, g32p_row07_traceSegment_039_1488_0015, g32p_row07_traceSegment_039_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_039 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1458 30 30, g32p_row07_traceSegment_039_1458_0030, g32p_row07_traceSegment_039_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1518 15 15, g32p_row07_traceSegment_039_1518_0015, g32p_row07_traceSegment_039_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1548 15 16, g32p_row07_traceSegment_039_1548_0015, g32p_row07_traceSegment_039_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1518 30 31, g32p_row07_traceSegment_039_1518_0030, g32p_row07_traceSegment_039_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_039 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1458 60 61, g32p_row07_traceSegment_039_1458_0060, g32p_row07_traceSegment_039_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1579 15 15, g32p_row07_traceSegment_039_1579_0015, g32p_row07_traceSegment_039_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1609 15 16, g32p_row07_traceSegment_039_1609_0015, g32p_row07_traceSegment_039_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1579 30 31, g32p_row07_traceSegment_039_1579_0030, g32p_row07_traceSegment_039_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1640 15 15, g32p_row07_traceSegment_039_1640_0015, g32p_row07_traceSegment_039_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1670 15 16, g32p_row07_traceSegment_039_1670_0015, g32p_row07_traceSegment_039_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1640 30 31, g32p_row07_traceSegment_039_1640_0030, g32p_row07_traceSegment_039_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_039 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1579 61 61, g32p_row07_traceSegment_039_1579_0061, g32p_row07_traceSegment_039_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_039 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1458 121 122, g32p_row07_traceSegment_039_1458_0121, g32p_row07_traceSegment_039_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1716 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1701 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1701 15 15, g32p_row07_traceSegment_039_1701_0015, g32p_row07_traceSegment_039_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1731 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1746 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1731 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1731 15 15, g32p_row07_traceSegment_039_1731_0015, g32p_row07_traceSegment_039_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_039 1701 60 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1701 30 30, g32p_row07_traceSegment_039_1701_0030, g32p_row07_traceSegment_039_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1761 15 15, g32p_row07_traceSegment_039_1761_0015, g32p_row07_traceSegment_039_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1791 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1791 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1791 15 16, g32p_row07_traceSegment_039_1791_0015, g32p_row07_traceSegment_039_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1761 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1761 30 31, g32p_row07_traceSegment_039_1761_0030, g32p_row07_traceSegment_039_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_039 1701 121 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1701 60 61, g32p_row07_traceSegment_039_1701_0060, g32p_row07_traceSegment_039_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1822 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1837 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1822 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1822 15 15, g32p_row07_traceSegment_039_1822_0015, g32p_row07_traceSegment_039_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1852 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1852 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1852 15 16, g32p_row07_traceSegment_039_1852_0015, g32p_row07_traceSegment_039_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1822 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1822 30 31, g32p_row07_traceSegment_039_1822_0030, g32p_row07_traceSegment_039_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1898 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_039 1883 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1883 15 15, g32p_row07_traceSegment_039_1883_0015, g32p_row07_traceSegment_039_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_039 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_039 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_039_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_039 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1913 15 16, g32p_row07_traceSegment_039_1913_0015, g32p_row07_traceSegment_039_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_039 1883 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1883 30 31, g32p_row07_traceSegment_039_1883_0030, g32p_row07_traceSegment_039_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_039 1822 122 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1822 61 61, g32p_row07_traceSegment_039_1822_0061, g32p_row07_traceSegment_039_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_039 1701 243 = [13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1701 121 122, g32p_row07_traceSegment_039_1701_0121, g32p_row07_traceSegment_039_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_039_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_039 1458 486 = [13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 1458 243 243, g32p_row07_traceSegment_039_1458_0243, g32p_row07_traceSegment_039_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_039 972 972 = [13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 972 486 486, g32p_row07_traceSegment_039_0972_0486, g32p_row07_traceSegment_039_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_039_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_039 0 1944 = [72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_039 0 972 972, g32p_row07_traceSegment_039_0000_0972, g32p_row07_traceSegment_039_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_039 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 39 = [72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_039_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_042 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 42 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_042_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 15 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 0 15 15, g32p_row07_traceSegment_042_0000_0015, g32p_row07_traceSegment_042_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 30 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 45 15 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 30 30 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 30 15 15, g32p_row07_traceSegment_042_0030_0015, g32p_row07_traceSegment_042_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_042 0 60 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 0 30 30, g32p_row07_traceSegment_042_0000_0030, g32p_row07_traceSegment_042_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 60 15 15, g32p_row07_traceSegment_042_0060_0015, g32p_row07_traceSegment_042_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 90 15 16, g32p_row07_traceSegment_042_0090_0015, g32p_row07_traceSegment_042_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 60 30 31, g32p_row07_traceSegment_042_0060_0030, g32p_row07_traceSegment_042_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_042 0 121 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 0 60 61, g32p_row07_traceSegment_042_0000_0060, g32p_row07_traceSegment_042_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 121 15 15, g32p_row07_traceSegment_042_0121_0015, g32p_row07_traceSegment_042_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 151 15 16, g32p_row07_traceSegment_042_0151_0015, g32p_row07_traceSegment_042_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 121 30 31, g32p_row07_traceSegment_042_0121_0030, g32p_row07_traceSegment_042_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 182 15 15, g32p_row07_traceSegment_042_0182_0015, g32p_row07_traceSegment_042_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 212 15 16, g32p_row07_traceSegment_042_0212_0015, g32p_row07_traceSegment_042_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 182 30 31, g32p_row07_traceSegment_042_0182_0030, g32p_row07_traceSegment_042_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_042 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 121 61 61, g32p_row07_traceSegment_042_0121_0061, g32p_row07_traceSegment_042_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_042 0 243 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 0 121 122, g32p_row07_traceSegment_042_0000_0121, g32p_row07_traceSegment_042_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 243 15 15, g32p_row07_traceSegment_042_0243_0015, g32p_row07_traceSegment_042_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 273 15 15, g32p_row07_traceSegment_042_0273_0015, g32p_row07_traceSegment_042_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_042 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 243 30 30, g32p_row07_traceSegment_042_0243_0030, g32p_row07_traceSegment_042_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 303 15 15, g32p_row07_traceSegment_042_0303_0015, g32p_row07_traceSegment_042_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 333 15 16, g32p_row07_traceSegment_042_0333_0015, g32p_row07_traceSegment_042_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 303 30 31, g32p_row07_traceSegment_042_0303_0030, g32p_row07_traceSegment_042_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_042 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 243 60 61, g32p_row07_traceSegment_042_0243_0060, g32p_row07_traceSegment_042_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 379 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 364 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 364 15 15, g32p_row07_traceSegment_042_0364_0015, g32p_row07_traceSegment_042_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 394 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 409 16 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 394 31 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 394 15 16, g32p_row07_traceSegment_042_0394_0015, g32p_row07_traceSegment_042_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 364 61 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 364 30 31, g32p_row07_traceSegment_042_0364_0030, g32p_row07_traceSegment_042_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 440 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 425 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 425 15 15, g32p_row07_traceSegment_042_0425_0015, g32p_row07_traceSegment_042_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 455 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 470 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 455 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 455 15 16, g32p_row07_traceSegment_042_0455_0015, g32p_row07_traceSegment_042_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 425 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 425 30 31, g32p_row07_traceSegment_042_0425_0030, g32p_row07_traceSegment_042_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_042 364 122 = [12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 364 61 61, g32p_row07_traceSegment_042_0364_0061, g32p_row07_traceSegment_042_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_042 243 243 = [12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 243 121 122, g32p_row07_traceSegment_042_0243_0121, g32p_row07_traceSegment_042_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_042 0 486 = [20] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 0 243 243, g32p_row07_traceSegment_042_0000_0243, g32p_row07_traceSegment_042_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 486 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 501 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 486 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 486 15 15, g32p_row07_traceSegment_042_0486_0015, g32p_row07_traceSegment_042_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 531 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 516 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 516 15 15, g32p_row07_traceSegment_042_0516_0015, g32p_row07_traceSegment_042_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_042 486 60 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 486 30 30, g32p_row07_traceSegment_042_0486_0030, g32p_row07_traceSegment_042_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 546 15 15, g32p_row07_traceSegment_042_0546_0015, g32p_row07_traceSegment_042_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 576 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 591 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 576 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 576 15 16, g32p_row07_traceSegment_042_0576_0015, g32p_row07_traceSegment_042_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 546 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 546 30 31, g32p_row07_traceSegment_042_0546_0030, g32p_row07_traceSegment_042_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_042 486 121 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 486 60 61, g32p_row07_traceSegment_042_0486_0060, g32p_row07_traceSegment_042_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 607 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 622 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 607 30 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 607 15 15, g32p_row07_traceSegment_042_0607_0015, g32p_row07_traceSegment_042_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 652 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 637 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 637 15 16, g32p_row07_traceSegment_042_0637_0015, g32p_row07_traceSegment_042_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 607 61 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 607 30 31, g32p_row07_traceSegment_042_0607_0030, g32p_row07_traceSegment_042_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 683 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 668 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 668 15 15, g32p_row07_traceSegment_042_0668_0015, g32p_row07_traceSegment_042_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 713 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 698 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 698 15 16, g32p_row07_traceSegment_042_0698_0015, g32p_row07_traceSegment_042_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 668 61 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 668 30 31, g32p_row07_traceSegment_042_0668_0030, g32p_row07_traceSegment_042_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_042 607 122 = [15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 607 61 61, g32p_row07_traceSegment_042_0607_0061, g32p_row07_traceSegment_042_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_042 486 243 = [22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 486 121 122, g32p_row07_traceSegment_042_0486_0121, g32p_row07_traceSegment_042_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 729 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 744 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 729 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 729 15 15, g32p_row07_traceSegment_042_0729_0015, g32p_row07_traceSegment_042_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 759 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 759 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 759 15 15, g32p_row07_traceSegment_042_0759_0015, g32p_row07_traceSegment_042_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_042 729 60 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 729 30 30, g32p_row07_traceSegment_042_0729_0030, g32p_row07_traceSegment_042_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 789 15 15, g32p_row07_traceSegment_042_0789_0015, g32p_row07_traceSegment_042_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 819 15 16, g32p_row07_traceSegment_042_0819_0015, g32p_row07_traceSegment_042_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 789 30 31, g32p_row07_traceSegment_042_0789_0030, g32p_row07_traceSegment_042_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_042 729 121 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 729 60 61, g32p_row07_traceSegment_042_0729_0060, g32p_row07_traceSegment_042_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 850 15 15, g32p_row07_traceSegment_042_0850_0015, g32p_row07_traceSegment_042_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 880 15 16, g32p_row07_traceSegment_042_0880_0015, g32p_row07_traceSegment_042_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 850 30 31, g32p_row07_traceSegment_042_0850_0030, g32p_row07_traceSegment_042_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 911 15 15, g32p_row07_traceSegment_042_0911_0015, g32p_row07_traceSegment_042_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 941 15 16, g32p_row07_traceSegment_042_0941_0015, g32p_row07_traceSegment_042_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 911 30 31, g32p_row07_traceSegment_042_0911_0030, g32p_row07_traceSegment_042_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_042 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 850 61 61, g32p_row07_traceSegment_042_0850_0061, g32p_row07_traceSegment_042_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_042 729 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 729 121 122, g32p_row07_traceSegment_042_0729_0121, g32p_row07_traceSegment_042_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_042 486 486 = [27] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 486 243 243, g32p_row07_traceSegment_042_0486_0243, g32p_row07_traceSegment_042_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_042 0 972 = [47] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 0 486 486, g32p_row07_traceSegment_042_0000_0486, g32p_row07_traceSegment_042_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 972 15 15, g32p_row07_traceSegment_042_0972_0015, g32p_row07_traceSegment_042_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1002 15 15, g32p_row07_traceSegment_042_1002_0015, g32p_row07_traceSegment_042_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_042 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 972 30 30, g32p_row07_traceSegment_042_0972_0030, g32p_row07_traceSegment_042_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1032 15 15, g32p_row07_traceSegment_042_1032_0015, g32p_row07_traceSegment_042_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1062 15 16, g32p_row07_traceSegment_042_1062_0015, g32p_row07_traceSegment_042_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1032 30 31, g32p_row07_traceSegment_042_1032_0030, g32p_row07_traceSegment_042_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_042 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 972 60 61, g32p_row07_traceSegment_042_0972_0060, g32p_row07_traceSegment_042_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1093 15 15, g32p_row07_traceSegment_042_1093_0015, g32p_row07_traceSegment_042_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1123 15 16, g32p_row07_traceSegment_042_1123_0015, g32p_row07_traceSegment_042_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1093 30 31, g32p_row07_traceSegment_042_1093_0030, g32p_row07_traceSegment_042_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1154 15 15, g32p_row07_traceSegment_042_1154_0015, g32p_row07_traceSegment_042_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1184 15 16, g32p_row07_traceSegment_042_1184_0015, g32p_row07_traceSegment_042_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1154 30 31, g32p_row07_traceSegment_042_1154_0030, g32p_row07_traceSegment_042_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_042 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1093 61 61, g32p_row07_traceSegment_042_1093_0061, g32p_row07_traceSegment_042_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_042 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 972 121 122, g32p_row07_traceSegment_042_0972_0121, g32p_row07_traceSegment_042_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1215 15 15, g32p_row07_traceSegment_042_1215_0015, g32p_row07_traceSegment_042_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1245 15 15, g32p_row07_traceSegment_042_1245_0015, g32p_row07_traceSegment_042_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_042 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1215 30 30, g32p_row07_traceSegment_042_1215_0030, g32p_row07_traceSegment_042_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1275 15 15, g32p_row07_traceSegment_042_1275_0015, g32p_row07_traceSegment_042_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1305 15 16, g32p_row07_traceSegment_042_1305_0015, g32p_row07_traceSegment_042_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1275 30 31, g32p_row07_traceSegment_042_1275_0030, g32p_row07_traceSegment_042_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_042 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1215 60 61, g32p_row07_traceSegment_042_1215_0060, g32p_row07_traceSegment_042_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1336 15 15, g32p_row07_traceSegment_042_1336_0015, g32p_row07_traceSegment_042_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1366 15 16, g32p_row07_traceSegment_042_1366_0015, g32p_row07_traceSegment_042_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1336 30 31, g32p_row07_traceSegment_042_1336_0030, g32p_row07_traceSegment_042_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1397 15 15, g32p_row07_traceSegment_042_1397_0015, g32p_row07_traceSegment_042_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1427 15 16, g32p_row07_traceSegment_042_1427_0015, g32p_row07_traceSegment_042_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1397 30 31, g32p_row07_traceSegment_042_1397_0030, g32p_row07_traceSegment_042_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_042 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1336 61 61, g32p_row07_traceSegment_042_1336_0061, g32p_row07_traceSegment_042_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_042 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1215 121 122, g32p_row07_traceSegment_042_1215_0121, g32p_row07_traceSegment_042_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_042 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 972 243 243, g32p_row07_traceSegment_042_0972_0243, g32p_row07_traceSegment_042_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1458 15 15, g32p_row07_traceSegment_042_1458_0015, g32p_row07_traceSegment_042_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1488 15 15, g32p_row07_traceSegment_042_1488_0015, g32p_row07_traceSegment_042_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_042 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1458 30 30, g32p_row07_traceSegment_042_1458_0030, g32p_row07_traceSegment_042_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1518 15 15, g32p_row07_traceSegment_042_1518_0015, g32p_row07_traceSegment_042_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1548 15 16, g32p_row07_traceSegment_042_1548_0015, g32p_row07_traceSegment_042_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1518 30 31, g32p_row07_traceSegment_042_1518_0030, g32p_row07_traceSegment_042_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_042 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1458 60 61, g32p_row07_traceSegment_042_1458_0060, g32p_row07_traceSegment_042_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1579 15 15, g32p_row07_traceSegment_042_1579_0015, g32p_row07_traceSegment_042_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1609 15 16, g32p_row07_traceSegment_042_1609_0015, g32p_row07_traceSegment_042_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1579 30 31, g32p_row07_traceSegment_042_1579_0030, g32p_row07_traceSegment_042_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1640 15 15, g32p_row07_traceSegment_042_1640_0015, g32p_row07_traceSegment_042_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1670 15 16, g32p_row07_traceSegment_042_1670_0015, g32p_row07_traceSegment_042_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1640 30 31, g32p_row07_traceSegment_042_1640_0030, g32p_row07_traceSegment_042_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_042 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1579 61 61, g32p_row07_traceSegment_042_1579_0061, g32p_row07_traceSegment_042_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_042 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1458 121 122, g32p_row07_traceSegment_042_1458_0121, g32p_row07_traceSegment_042_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1701 15 15, g32p_row07_traceSegment_042_1701_0015, g32p_row07_traceSegment_042_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1731 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1731 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1731 15 15, g32p_row07_traceSegment_042_1731_0015, g32p_row07_traceSegment_042_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_042 1701 60 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1701 30 30, g32p_row07_traceSegment_042_1701_0030, g32p_row07_traceSegment_042_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1761 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1776 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1761 30 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1761 15 15, g32p_row07_traceSegment_042_1761_0015, g32p_row07_traceSegment_042_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1791 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1806 16 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1791 31 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1791 15 16, g32p_row07_traceSegment_042_1791_0015, g32p_row07_traceSegment_042_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1761 61 = [15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1761 30 31, g32p_row07_traceSegment_042_1761_0030, g32p_row07_traceSegment_042_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_042 1701 121 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1701 60 61, g32p_row07_traceSegment_042_1701_0060, g32p_row07_traceSegment_042_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1837 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1822 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1822 15 15, g32p_row07_traceSegment_042_1822_0015, g32p_row07_traceSegment_042_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1852 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1867 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1852 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1852 15 16, g32p_row07_traceSegment_042_1852_0015, g32p_row07_traceSegment_042_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1822 61 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1822 30 31, g32p_row07_traceSegment_042_1822_0030, g32p_row07_traceSegment_042_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1883 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_042 1883 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1883 15 15, g32p_row07_traceSegment_042_1883_0015, g32p_row07_traceSegment_042_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_042 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_042 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_042_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_042 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1913 15 16, g32p_row07_traceSegment_042_1913_0015, g32p_row07_traceSegment_042_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_042 1883 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1883 30 31, g32p_row07_traceSegment_042_1883_0030, g32p_row07_traceSegment_042_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_042 1822 122 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1822 61 61, g32p_row07_traceSegment_042_1822_0061, g32p_row07_traceSegment_042_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_042 1701 243 = [25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1701 121 122, g32p_row07_traceSegment_042_1701_0121, g32p_row07_traceSegment_042_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_042_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_042 1458 486 = [25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 1458 243 243, g32p_row07_traceSegment_042_1458_0243, g32p_row07_traceSegment_042_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_042 972 972 = [25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 972 486 486, g32p_row07_traceSegment_042_0972_0486, g32p_row07_traceSegment_042_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_042_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_042 0 1944 = [72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_042 0 972 972, g32p_row07_traceSegment_042_0000_0972, g32p_row07_traceSegment_042_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_042 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 42 = [72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_042_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_044 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 44 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_044_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 15 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 0 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 0 15 15, g32p_row07_traceSegment_044_0000_0015, g32p_row07_traceSegment_044_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 30 15 15, g32p_row07_traceSegment_044_0030_0015, g32p_row07_traceSegment_044_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_044 0 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 0 30 30, g32p_row07_traceSegment_044_0000_0030, g32p_row07_traceSegment_044_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 60 15 15, g32p_row07_traceSegment_044_0060_0015, g32p_row07_traceSegment_044_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 90 15 16, g32p_row07_traceSegment_044_0090_0015, g32p_row07_traceSegment_044_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 60 30 31, g32p_row07_traceSegment_044_0060_0030, g32p_row07_traceSegment_044_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_044 0 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 0 60 61, g32p_row07_traceSegment_044_0000_0060, g32p_row07_traceSegment_044_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 121 15 15, g32p_row07_traceSegment_044_0121_0015, g32p_row07_traceSegment_044_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 151 15 16, g32p_row07_traceSegment_044_0151_0015, g32p_row07_traceSegment_044_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 121 30 31, g32p_row07_traceSegment_044_0121_0030, g32p_row07_traceSegment_044_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 182 15 15, g32p_row07_traceSegment_044_0182_0015, g32p_row07_traceSegment_044_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 212 15 16, g32p_row07_traceSegment_044_0212_0015, g32p_row07_traceSegment_044_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 182 30 31, g32p_row07_traceSegment_044_0182_0030, g32p_row07_traceSegment_044_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_044 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 121 61 61, g32p_row07_traceSegment_044_0121_0061, g32p_row07_traceSegment_044_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_044 0 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 0 121 122, g32p_row07_traceSegment_044_0000_0121, g32p_row07_traceSegment_044_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 243 15 15, g32p_row07_traceSegment_044_0243_0015, g32p_row07_traceSegment_044_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 273 15 15, g32p_row07_traceSegment_044_0273_0015, g32p_row07_traceSegment_044_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_044 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 243 30 30, g32p_row07_traceSegment_044_0243_0030, g32p_row07_traceSegment_044_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 303 15 15, g32p_row07_traceSegment_044_0303_0015, g32p_row07_traceSegment_044_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 333 15 16, g32p_row07_traceSegment_044_0333_0015, g32p_row07_traceSegment_044_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 303 30 31, g32p_row07_traceSegment_044_0303_0030, g32p_row07_traceSegment_044_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_044 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 243 60 61, g32p_row07_traceSegment_044_0243_0060, g32p_row07_traceSegment_044_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 364 15 15, g32p_row07_traceSegment_044_0364_0015, g32p_row07_traceSegment_044_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 394 15 16, g32p_row07_traceSegment_044_0394_0015, g32p_row07_traceSegment_044_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 364 30 31, g32p_row07_traceSegment_044_0364_0030, g32p_row07_traceSegment_044_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 425 15 15, g32p_row07_traceSegment_044_0425_0015, g32p_row07_traceSegment_044_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 470 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 455 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 455 15 16, g32p_row07_traceSegment_044_0455_0015, g32p_row07_traceSegment_044_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 425 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 425 30 31, g32p_row07_traceSegment_044_0425_0030, g32p_row07_traceSegment_044_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_044 364 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 364 61 61, g32p_row07_traceSegment_044_0364_0061, g32p_row07_traceSegment_044_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_044 243 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 243 121 122, g32p_row07_traceSegment_044_0243_0121, g32p_row07_traceSegment_044_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_044 0 486 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 0 243 243, g32p_row07_traceSegment_044_0000_0243, g32p_row07_traceSegment_044_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 486 15 15, g32p_row07_traceSegment_044_0486_0015, g32p_row07_traceSegment_044_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 516 15 15, g32p_row07_traceSegment_044_0516_0015, g32p_row07_traceSegment_044_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_044 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 486 30 30, g32p_row07_traceSegment_044_0486_0030, g32p_row07_traceSegment_044_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 546 15 15, g32p_row07_traceSegment_044_0546_0015, g32p_row07_traceSegment_044_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 576 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 576 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 576 15 16, g32p_row07_traceSegment_044_0576_0015, g32p_row07_traceSegment_044_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 546 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 546 30 31, g32p_row07_traceSegment_044_0546_0030, g32p_row07_traceSegment_044_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_044 486 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 486 60 61, g32p_row07_traceSegment_044_0486_0060, g32p_row07_traceSegment_044_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 607 15 15, g32p_row07_traceSegment_044_0607_0015, g32p_row07_traceSegment_044_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 637 15 16, g32p_row07_traceSegment_044_0637_0015, g32p_row07_traceSegment_044_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 607 30 31, g32p_row07_traceSegment_044_0607_0030, g32p_row07_traceSegment_044_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 668 15 15, g32p_row07_traceSegment_044_0668_0015, g32p_row07_traceSegment_044_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 698 15 16, g32p_row07_traceSegment_044_0698_0015, g32p_row07_traceSegment_044_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 668 30 31, g32p_row07_traceSegment_044_0668_0030, g32p_row07_traceSegment_044_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_044 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 607 61 61, g32p_row07_traceSegment_044_0607_0061, g32p_row07_traceSegment_044_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_044 486 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 486 121 122, g32p_row07_traceSegment_044_0486_0121, g32p_row07_traceSegment_044_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 729 15 15, g32p_row07_traceSegment_044_0729_0015, g32p_row07_traceSegment_044_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 759 15 15, g32p_row07_traceSegment_044_0759_0015, g32p_row07_traceSegment_044_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_044 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 729 30 30, g32p_row07_traceSegment_044_0729_0030, g32p_row07_traceSegment_044_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 789 15 15, g32p_row07_traceSegment_044_0789_0015, g32p_row07_traceSegment_044_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 819 15 16, g32p_row07_traceSegment_044_0819_0015, g32p_row07_traceSegment_044_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 789 30 31, g32p_row07_traceSegment_044_0789_0030, g32p_row07_traceSegment_044_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_044 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 729 60 61, g32p_row07_traceSegment_044_0729_0060, g32p_row07_traceSegment_044_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 850 15 15, g32p_row07_traceSegment_044_0850_0015, g32p_row07_traceSegment_044_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 880 15 16, g32p_row07_traceSegment_044_0880_0015, g32p_row07_traceSegment_044_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 850 30 31, g32p_row07_traceSegment_044_0850_0030, g32p_row07_traceSegment_044_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 911 15 15, g32p_row07_traceSegment_044_0911_0015, g32p_row07_traceSegment_044_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 941 15 16, g32p_row07_traceSegment_044_0941_0015, g32p_row07_traceSegment_044_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 911 30 31, g32p_row07_traceSegment_044_0911_0030, g32p_row07_traceSegment_044_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_044 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 850 61 61, g32p_row07_traceSegment_044_0850_0061, g32p_row07_traceSegment_044_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_044 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 729 121 122, g32p_row07_traceSegment_044_0729_0121, g32p_row07_traceSegment_044_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_044 486 486 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 486 243 243, g32p_row07_traceSegment_044_0486_0243, g32p_row07_traceSegment_044_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_044 0 972 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 0 486 486, g32p_row07_traceSegment_044_0000_0486, g32p_row07_traceSegment_044_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 972 15 15, g32p_row07_traceSegment_044_0972_0015, g32p_row07_traceSegment_044_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1002 15 15, g32p_row07_traceSegment_044_1002_0015, g32p_row07_traceSegment_044_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_044 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 972 30 30, g32p_row07_traceSegment_044_0972_0030, g32p_row07_traceSegment_044_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1032 15 15, g32p_row07_traceSegment_044_1032_0015, g32p_row07_traceSegment_044_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1062 15 16, g32p_row07_traceSegment_044_1062_0015, g32p_row07_traceSegment_044_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1032 30 31, g32p_row07_traceSegment_044_1032_0030, g32p_row07_traceSegment_044_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_044 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 972 60 61, g32p_row07_traceSegment_044_0972_0060, g32p_row07_traceSegment_044_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1093 15 15, g32p_row07_traceSegment_044_1093_0015, g32p_row07_traceSegment_044_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1123 15 16, g32p_row07_traceSegment_044_1123_0015, g32p_row07_traceSegment_044_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1093 30 31, g32p_row07_traceSegment_044_1093_0030, g32p_row07_traceSegment_044_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1154 15 15, g32p_row07_traceSegment_044_1154_0015, g32p_row07_traceSegment_044_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1184 15 16, g32p_row07_traceSegment_044_1184_0015, g32p_row07_traceSegment_044_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1154 30 31, g32p_row07_traceSegment_044_1154_0030, g32p_row07_traceSegment_044_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_044 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1093 61 61, g32p_row07_traceSegment_044_1093_0061, g32p_row07_traceSegment_044_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_044 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 972 121 122, g32p_row07_traceSegment_044_0972_0121, g32p_row07_traceSegment_044_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1215 15 15, g32p_row07_traceSegment_044_1215_0015, g32p_row07_traceSegment_044_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1245 15 15, g32p_row07_traceSegment_044_1245_0015, g32p_row07_traceSegment_044_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_044 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1215 30 30, g32p_row07_traceSegment_044_1215_0030, g32p_row07_traceSegment_044_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1275 15 15, g32p_row07_traceSegment_044_1275_0015, g32p_row07_traceSegment_044_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1305 15 16, g32p_row07_traceSegment_044_1305_0015, g32p_row07_traceSegment_044_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1275 30 31, g32p_row07_traceSegment_044_1275_0030, g32p_row07_traceSegment_044_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_044 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1215 60 61, g32p_row07_traceSegment_044_1215_0060, g32p_row07_traceSegment_044_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1336 15 15, g32p_row07_traceSegment_044_1336_0015, g32p_row07_traceSegment_044_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1366 15 16, g32p_row07_traceSegment_044_1366_0015, g32p_row07_traceSegment_044_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1336 30 31, g32p_row07_traceSegment_044_1336_0030, g32p_row07_traceSegment_044_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1397 15 15, g32p_row07_traceSegment_044_1397_0015, g32p_row07_traceSegment_044_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1427 15 16, g32p_row07_traceSegment_044_1427_0015, g32p_row07_traceSegment_044_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1397 30 31, g32p_row07_traceSegment_044_1397_0030, g32p_row07_traceSegment_044_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_044 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1336 61 61, g32p_row07_traceSegment_044_1336_0061, g32p_row07_traceSegment_044_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_044 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1215 121 122, g32p_row07_traceSegment_044_1215_0121, g32p_row07_traceSegment_044_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_044 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 972 243 243, g32p_row07_traceSegment_044_0972_0243, g32p_row07_traceSegment_044_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1458 15 15, g32p_row07_traceSegment_044_1458_0015, g32p_row07_traceSegment_044_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1488 15 15, g32p_row07_traceSegment_044_1488_0015, g32p_row07_traceSegment_044_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_044 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1458 30 30, g32p_row07_traceSegment_044_1458_0030, g32p_row07_traceSegment_044_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1518 15 15, g32p_row07_traceSegment_044_1518_0015, g32p_row07_traceSegment_044_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1548 15 16, g32p_row07_traceSegment_044_1548_0015, g32p_row07_traceSegment_044_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1518 30 31, g32p_row07_traceSegment_044_1518_0030, g32p_row07_traceSegment_044_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_044 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1458 60 61, g32p_row07_traceSegment_044_1458_0060, g32p_row07_traceSegment_044_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1579 15 15, g32p_row07_traceSegment_044_1579_0015, g32p_row07_traceSegment_044_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1609 15 16, g32p_row07_traceSegment_044_1609_0015, g32p_row07_traceSegment_044_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1579 30 31, g32p_row07_traceSegment_044_1579_0030, g32p_row07_traceSegment_044_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1640 15 15, g32p_row07_traceSegment_044_1640_0015, g32p_row07_traceSegment_044_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1670 15 16, g32p_row07_traceSegment_044_1670_0015, g32p_row07_traceSegment_044_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1640 30 31, g32p_row07_traceSegment_044_1640_0030, g32p_row07_traceSegment_044_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_044 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1579 61 61, g32p_row07_traceSegment_044_1579_0061, g32p_row07_traceSegment_044_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_044 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1458 121 122, g32p_row07_traceSegment_044_1458_0121, g32p_row07_traceSegment_044_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1701 15 15, g32p_row07_traceSegment_044_1701_0015, g32p_row07_traceSegment_044_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1731 15 15, g32p_row07_traceSegment_044_1731_0015, g32p_row07_traceSegment_044_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_044 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1701 30 30, g32p_row07_traceSegment_044_1701_0030, g32p_row07_traceSegment_044_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1761 15 15, g32p_row07_traceSegment_044_1761_0015, g32p_row07_traceSegment_044_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1791 15 16, g32p_row07_traceSegment_044_1791_0015, g32p_row07_traceSegment_044_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1761 30 31, g32p_row07_traceSegment_044_1761_0030, g32p_row07_traceSegment_044_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_044 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1701 60 61, g32p_row07_traceSegment_044_1701_0060, g32p_row07_traceSegment_044_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1822 15 15, g32p_row07_traceSegment_044_1822_0015, g32p_row07_traceSegment_044_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1852 15 16, g32p_row07_traceSegment_044_1852_0015, g32p_row07_traceSegment_044_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1822 30 31, g32p_row07_traceSegment_044_1822_0030, g32p_row07_traceSegment_044_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_044 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1883 15 15, g32p_row07_traceSegment_044_1883_0015, g32p_row07_traceSegment_044_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_044 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_044 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_044_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_044 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1913 15 16, g32p_row07_traceSegment_044_1913_0015, g32p_row07_traceSegment_044_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_044 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1883 30 31, g32p_row07_traceSegment_044_1883_0030, g32p_row07_traceSegment_044_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_044 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1822 61 61, g32p_row07_traceSegment_044_1822_0061, g32p_row07_traceSegment_044_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_044 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1701 121 122, g32p_row07_traceSegment_044_1701_0121, g32p_row07_traceSegment_044_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_044_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_044 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 1458 243 243, g32p_row07_traceSegment_044_1458_0243, g32p_row07_traceSegment_044_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_044 972 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 972 486 486, g32p_row07_traceSegment_044_0972_0486, g32p_row07_traceSegment_044_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_044_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_044 0 1944 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_044 0 972 972, g32p_row07_traceSegment_044_0000_0972, g32p_row07_traceSegment_044_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 44 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_044_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_045 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 45 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_045_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 0 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 15 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 0 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 0 15 15, g32p_row07_traceSegment_045_0000_0015, g32p_row07_traceSegment_045_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 30 15 15, g32p_row07_traceSegment_045_0030_0015, g32p_row07_traceSegment_045_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_045 0 60 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 0 30 30, g32p_row07_traceSegment_045_0000_0030, g32p_row07_traceSegment_045_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 60 15 15, g32p_row07_traceSegment_045_0060_0015, g32p_row07_traceSegment_045_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 90 15 16, g32p_row07_traceSegment_045_0090_0015, g32p_row07_traceSegment_045_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 60 30 31, g32p_row07_traceSegment_045_0060_0030, g32p_row07_traceSegment_045_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_045 0 121 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 0 60 61, g32p_row07_traceSegment_045_0000_0060, g32p_row07_traceSegment_045_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 121 15 15, g32p_row07_traceSegment_045_0121_0015, g32p_row07_traceSegment_045_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 151 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 166 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 151 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 151 15 16, g32p_row07_traceSegment_045_0151_0015, g32p_row07_traceSegment_045_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 121 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 121 30 31, g32p_row07_traceSegment_045_0121_0030, g32p_row07_traceSegment_045_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 182 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 197 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 182 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 182 15 15, g32p_row07_traceSegment_045_0182_0015, g32p_row07_traceSegment_045_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 212 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 212 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 212 15 16, g32p_row07_traceSegment_045_0212_0015, g32p_row07_traceSegment_045_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 182 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 182 30 31, g32p_row07_traceSegment_045_0182_0030, g32p_row07_traceSegment_045_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_045 121 122 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 121 61 61, g32p_row07_traceSegment_045_0121_0061, g32p_row07_traceSegment_045_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_045 0 243 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 0 121 122, g32p_row07_traceSegment_045_0000_0121, g32p_row07_traceSegment_045_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 243 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 258 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 243 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 243 15 15, g32p_row07_traceSegment_045_0243_0015, g32p_row07_traceSegment_045_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 273 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 288 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 273 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 273 15 15, g32p_row07_traceSegment_045_0273_0015, g32p_row07_traceSegment_045_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_045 243 60 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 243 30 30, g32p_row07_traceSegment_045_0243_0030, g32p_row07_traceSegment_045_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 303 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 318 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 303 30 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 303 15 15, g32p_row07_traceSegment_045_0303_0015, g32p_row07_traceSegment_045_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 333 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 348 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 333 31 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 333 15 16, g32p_row07_traceSegment_045_0333_0015, g32p_row07_traceSegment_045_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 303 61 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 303 30 31, g32p_row07_traceSegment_045_0303_0030, g32p_row07_traceSegment_045_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_045 243 121 = [0, 19] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 243 60 61, g32p_row07_traceSegment_045_0243_0060, g32p_row07_traceSegment_045_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 364 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 364 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 364 15 15, g32p_row07_traceSegment_045_0364_0015, g32p_row07_traceSegment_045_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 394 15 16, g32p_row07_traceSegment_045_0394_0015, g32p_row07_traceSegment_045_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 364 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 364 30 31, g32p_row07_traceSegment_045_0364_0030, g32p_row07_traceSegment_045_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 425 15 15, g32p_row07_traceSegment_045_0425_0015, g32p_row07_traceSegment_045_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 455 15 16, g32p_row07_traceSegment_045_0455_0015, g32p_row07_traceSegment_045_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 425 30 31, g32p_row07_traceSegment_045_0425_0030, g32p_row07_traceSegment_045_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_045 364 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 364 61 61, g32p_row07_traceSegment_045_0364_0061, g32p_row07_traceSegment_045_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_045 243 243 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 243 121 122, g32p_row07_traceSegment_045_0243_0121, g32p_row07_traceSegment_045_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_045 0 486 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 0 243 243, g32p_row07_traceSegment_045_0000_0243, g32p_row07_traceSegment_045_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 486 15 15, g32p_row07_traceSegment_045_0486_0015, g32p_row07_traceSegment_045_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 516 15 15, g32p_row07_traceSegment_045_0516_0015, g32p_row07_traceSegment_045_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_045 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 486 30 30, g32p_row07_traceSegment_045_0486_0030, g32p_row07_traceSegment_045_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 546 15 15, g32p_row07_traceSegment_045_0546_0015, g32p_row07_traceSegment_045_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 576 15 16, g32p_row07_traceSegment_045_0576_0015, g32p_row07_traceSegment_045_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 546 30 31, g32p_row07_traceSegment_045_0546_0030, g32p_row07_traceSegment_045_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_045 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 486 60 61, g32p_row07_traceSegment_045_0486_0060, g32p_row07_traceSegment_045_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 607 15 15, g32p_row07_traceSegment_045_0607_0015, g32p_row07_traceSegment_045_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 637 15 16, g32p_row07_traceSegment_045_0637_0015, g32p_row07_traceSegment_045_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 607 30 31, g32p_row07_traceSegment_045_0607_0030, g32p_row07_traceSegment_045_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 668 15 15, g32p_row07_traceSegment_045_0668_0015, g32p_row07_traceSegment_045_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 698 15 16, g32p_row07_traceSegment_045_0698_0015, g32p_row07_traceSegment_045_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 668 30 31, g32p_row07_traceSegment_045_0668_0030, g32p_row07_traceSegment_045_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_045 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 607 61 61, g32p_row07_traceSegment_045_0607_0061, g32p_row07_traceSegment_045_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_045 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 486 121 122, g32p_row07_traceSegment_045_0486_0121, g32p_row07_traceSegment_045_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 729 15 15, g32p_row07_traceSegment_045_0729_0015, g32p_row07_traceSegment_045_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 759 15 15, g32p_row07_traceSegment_045_0759_0015, g32p_row07_traceSegment_045_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_045 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 729 30 30, g32p_row07_traceSegment_045_0729_0030, g32p_row07_traceSegment_045_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 789 15 15, g32p_row07_traceSegment_045_0789_0015, g32p_row07_traceSegment_045_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 819 15 16, g32p_row07_traceSegment_045_0819_0015, g32p_row07_traceSegment_045_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 789 30 31, g32p_row07_traceSegment_045_0789_0030, g32p_row07_traceSegment_045_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_045 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 729 60 61, g32p_row07_traceSegment_045_0729_0060, g32p_row07_traceSegment_045_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 850 15 15, g32p_row07_traceSegment_045_0850_0015, g32p_row07_traceSegment_045_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 880 15 16, g32p_row07_traceSegment_045_0880_0015, g32p_row07_traceSegment_045_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 850 30 31, g32p_row07_traceSegment_045_0850_0030, g32p_row07_traceSegment_045_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 911 15 15, g32p_row07_traceSegment_045_0911_0015, g32p_row07_traceSegment_045_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 941 15 16, g32p_row07_traceSegment_045_0941_0015, g32p_row07_traceSegment_045_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 911 30 31, g32p_row07_traceSegment_045_0911_0030, g32p_row07_traceSegment_045_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_045 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 850 61 61, g32p_row07_traceSegment_045_0850_0061, g32p_row07_traceSegment_045_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_045 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 729 121 122, g32p_row07_traceSegment_045_0729_0121, g32p_row07_traceSegment_045_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_045 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 486 243 243, g32p_row07_traceSegment_045_0486_0243, g32p_row07_traceSegment_045_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_045 0 972 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 0 486 486, g32p_row07_traceSegment_045_0000_0486, g32p_row07_traceSegment_045_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 972 15 15, g32p_row07_traceSegment_045_0972_0015, g32p_row07_traceSegment_045_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1002 15 15, g32p_row07_traceSegment_045_1002_0015, g32p_row07_traceSegment_045_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_045 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 972 30 30, g32p_row07_traceSegment_045_0972_0030, g32p_row07_traceSegment_045_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1032 15 15, g32p_row07_traceSegment_045_1032_0015, g32p_row07_traceSegment_045_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1062 15 16, g32p_row07_traceSegment_045_1062_0015, g32p_row07_traceSegment_045_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1032 30 31, g32p_row07_traceSegment_045_1032_0030, g32p_row07_traceSegment_045_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_045 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 972 60 61, g32p_row07_traceSegment_045_0972_0060, g32p_row07_traceSegment_045_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1093 15 15, g32p_row07_traceSegment_045_1093_0015, g32p_row07_traceSegment_045_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1123 15 16, g32p_row07_traceSegment_045_1123_0015, g32p_row07_traceSegment_045_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1093 30 31, g32p_row07_traceSegment_045_1093_0030, g32p_row07_traceSegment_045_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1154 15 15, g32p_row07_traceSegment_045_1154_0015, g32p_row07_traceSegment_045_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1184 15 16, g32p_row07_traceSegment_045_1184_0015, g32p_row07_traceSegment_045_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1154 30 31, g32p_row07_traceSegment_045_1154_0030, g32p_row07_traceSegment_045_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_045 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1093 61 61, g32p_row07_traceSegment_045_1093_0061, g32p_row07_traceSegment_045_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_045 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 972 121 122, g32p_row07_traceSegment_045_0972_0121, g32p_row07_traceSegment_045_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1215 15 15, g32p_row07_traceSegment_045_1215_0015, g32p_row07_traceSegment_045_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1245 15 15, g32p_row07_traceSegment_045_1245_0015, g32p_row07_traceSegment_045_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_045 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1215 30 30, g32p_row07_traceSegment_045_1215_0030, g32p_row07_traceSegment_045_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1275 15 15, g32p_row07_traceSegment_045_1275_0015, g32p_row07_traceSegment_045_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1305 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1320 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1305 31 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1305 15 16, g32p_row07_traceSegment_045_1305_0015, g32p_row07_traceSegment_045_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1275 61 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1275 30 31, g32p_row07_traceSegment_045_1275_0030, g32p_row07_traceSegment_045_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_045 1215 121 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1215 60 61, g32p_row07_traceSegment_045_1215_0060, g32p_row07_traceSegment_045_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1336 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1351 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1336 30 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1336 15 15, g32p_row07_traceSegment_045_1336_0015, g32p_row07_traceSegment_045_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1366 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1381 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1366 31 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1366 15 16, g32p_row07_traceSegment_045_1366_0015, g32p_row07_traceSegment_045_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1336 61 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1336 30 31, g32p_row07_traceSegment_045_1336_0030, g32p_row07_traceSegment_045_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1397 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1412 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1397 30 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1397 15 15, g32p_row07_traceSegment_045_1397_0015, g32p_row07_traceSegment_045_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1427 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1442 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1427 31 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1427 15 16, g32p_row07_traceSegment_045_1427_0015, g32p_row07_traceSegment_045_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1397 61 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1397 30 31, g32p_row07_traceSegment_045_1397_0030, g32p_row07_traceSegment_045_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_045 1336 122 = [0, 26] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1336 61 61, g32p_row07_traceSegment_045_1336_0061, g32p_row07_traceSegment_045_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_045 1215 243 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1215 121 122, g32p_row07_traceSegment_045_1215_0121, g32p_row07_traceSegment_045_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_045 972 486 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 972 243 243, g32p_row07_traceSegment_045_0972_0243, g32p_row07_traceSegment_045_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1458 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1473 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1458 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1458 15 15, g32p_row07_traceSegment_045_1458_0015, g32p_row07_traceSegment_045_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1488 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1503 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1488 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1488 15 15, g32p_row07_traceSegment_045_1488_0015, g32p_row07_traceSegment_045_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_045 1458 60 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1458 30 30, g32p_row07_traceSegment_045_1458_0030, g32p_row07_traceSegment_045_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1518 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1533 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1518 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1518 15 15, g32p_row07_traceSegment_045_1518_0015, g32p_row07_traceSegment_045_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1548 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1548 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1548 15 16, g32p_row07_traceSegment_045_1548_0015, g32p_row07_traceSegment_045_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1518 61 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1518 30 31, g32p_row07_traceSegment_045_1518_0030, g32p_row07_traceSegment_045_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_045 1458 121 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1458 60 61, g32p_row07_traceSegment_045_1458_0060, g32p_row07_traceSegment_045_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1579 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1579 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1579 15 15, g32p_row07_traceSegment_045_1579_0015, g32p_row07_traceSegment_045_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1609 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1624 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1609 31 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1609 15 16, g32p_row07_traceSegment_045_1609_0015, g32p_row07_traceSegment_045_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1579 61 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1579 30 31, g32p_row07_traceSegment_045_1579_0030, g32p_row07_traceSegment_045_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1640 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1655 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1640 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1640 15 15, g32p_row07_traceSegment_045_1640_0015, g32p_row07_traceSegment_045_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1670 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1685 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1670 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1670 15 16, g32p_row07_traceSegment_045_1670_0015, g32p_row07_traceSegment_045_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1640 61 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1640 30 31, g32p_row07_traceSegment_045_1640_0030, g32p_row07_traceSegment_045_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_045 1579 122 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1579 61 61, g32p_row07_traceSegment_045_1579_0061, g32p_row07_traceSegment_045_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_045 1458 243 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1458 121 122, g32p_row07_traceSegment_045_1458_0121, g32p_row07_traceSegment_045_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1701 15 15, g32p_row07_traceSegment_045_1701_0015, g32p_row07_traceSegment_045_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1731 15 15, g32p_row07_traceSegment_045_1731_0015, g32p_row07_traceSegment_045_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_045 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1701 30 30, g32p_row07_traceSegment_045_1701_0030, g32p_row07_traceSegment_045_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1761 15 15, g32p_row07_traceSegment_045_1761_0015, g32p_row07_traceSegment_045_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1791 15 16, g32p_row07_traceSegment_045_1791_0015, g32p_row07_traceSegment_045_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1761 30 31, g32p_row07_traceSegment_045_1761_0030, g32p_row07_traceSegment_045_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_045 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1701 60 61, g32p_row07_traceSegment_045_1701_0060, g32p_row07_traceSegment_045_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1822 15 15, g32p_row07_traceSegment_045_1822_0015, g32p_row07_traceSegment_045_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1852 15 16, g32p_row07_traceSegment_045_1852_0015, g32p_row07_traceSegment_045_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1822 30 31, g32p_row07_traceSegment_045_1822_0030, g32p_row07_traceSegment_045_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_045 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1883 15 15, g32p_row07_traceSegment_045_1883_0015, g32p_row07_traceSegment_045_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_045 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_045 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_045_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_045 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1913 15 16, g32p_row07_traceSegment_045_1913_0015, g32p_row07_traceSegment_045_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_045 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1883 30 31, g32p_row07_traceSegment_045_1883_0030, g32p_row07_traceSegment_045_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_045 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1822 61 61, g32p_row07_traceSegment_045_1822_0061, g32p_row07_traceSegment_045_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_045 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1701 121 122, g32p_row07_traceSegment_045_1701_0121, g32p_row07_traceSegment_045_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_045_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_045 1458 486 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 1458 243 243, g32p_row07_traceSegment_045_1458_0243, g32p_row07_traceSegment_045_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_045 972 972 = [0, 53] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 972 486 486, g32p_row07_traceSegment_045_0972_0486, g32p_row07_traceSegment_045_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_045_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_045 0 1944 = [0, 84] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_045 0 972 972, g32p_row07_traceSegment_045_0000_0972, g32p_row07_traceSegment_045_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 45 = [0, 84] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_045_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row07_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 34) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 34) (g32p_literalTraceValue 6 34)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row07_traceCoefficients_034]
  decide +kernel

theorem g32p_row07_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 35) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 35) (g32p_literalTraceValue 6 35)
      [1, 1, 1] [27216] = true := by
  rw [g32p_row07_traceCoefficients_035]
  decide +kernel

theorem g32p_row07_tracePolynomial_036 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 36) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 36) (g32p_literalTraceValue 6 36)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row07_traceCoefficients_036]
  decide +kernel

theorem g32p_row07_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 37) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 37) (g32p_literalTraceValue 6 37)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row07_traceCoefficients_037]
  decide +kernel

theorem g32p_row07_tracePolynomial_039 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 39) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 39) (g32p_literalTraceValue 6 39)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_039]
  decide +kernel

theorem g32p_row07_tracePolynomial_042 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 42) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 42) (g32p_literalTraceValue 6 42)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_042]
  decide +kernel

theorem g32p_row07_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 44) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 44) (g32p_literalTraceValue 6 44)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_044]
  decide +kernel

theorem g32p_row07_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 45) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 45) (g32p_literalTraceValue 6 45)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_045]
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

private def g32p_row07_traceSegment_046 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 46 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_046_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 0 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 0 30 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 0 15 15, g32p_row07_traceSegment_046_0000_0015, g32p_row07_traceSegment_046_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 30 15 15, g32p_row07_traceSegment_046_0030_0015, g32p_row07_traceSegment_046_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_046 0 60 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 0 30 30, g32p_row07_traceSegment_046_0000_0030, g32p_row07_traceSegment_046_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 60 15 15, g32p_row07_traceSegment_046_0060_0015, g32p_row07_traceSegment_046_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 90 15 16, g32p_row07_traceSegment_046_0090_0015, g32p_row07_traceSegment_046_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 60 30 31, g32p_row07_traceSegment_046_0060_0030, g32p_row07_traceSegment_046_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_046 0 121 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 0 60 61, g32p_row07_traceSegment_046_0000_0060, g32p_row07_traceSegment_046_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 121 15 15, g32p_row07_traceSegment_046_0121_0015, g32p_row07_traceSegment_046_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 151 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 166 16 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 151 31 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 151 15 16, g32p_row07_traceSegment_046_0151_0015, g32p_row07_traceSegment_046_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 121 61 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 121 30 31, g32p_row07_traceSegment_046_0121_0030, g32p_row07_traceSegment_046_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 182 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 197 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 182 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 182 15 15, g32p_row07_traceSegment_046_0182_0015, g32p_row07_traceSegment_046_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 212 15 16, g32p_row07_traceSegment_046_0212_0015, g32p_row07_traceSegment_046_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 182 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 182 30 31, g32p_row07_traceSegment_046_0182_0030, g32p_row07_traceSegment_046_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_046 121 122 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 121 61 61, g32p_row07_traceSegment_046_0121_0061, g32p_row07_traceSegment_046_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_046 0 243 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 0 121 122, g32p_row07_traceSegment_046_0000_0121, g32p_row07_traceSegment_046_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 243 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 258 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 243 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 243 15 15, g32p_row07_traceSegment_046_0243_0015, g32p_row07_traceSegment_046_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 273 15 15, g32p_row07_traceSegment_046_0273_0015, g32p_row07_traceSegment_046_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_046 243 60 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 243 30 30, g32p_row07_traceSegment_046_0243_0030, g32p_row07_traceSegment_046_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 303 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 318 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 303 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 303 15 15, g32p_row07_traceSegment_046_0303_0015, g32p_row07_traceSegment_046_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 333 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 348 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 333 31 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 333 15 16, g32p_row07_traceSegment_046_0333_0015, g32p_row07_traceSegment_046_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 303 61 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 303 30 31, g32p_row07_traceSegment_046_0303_0030, g32p_row07_traceSegment_046_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_046 243 121 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 243 60 61, g32p_row07_traceSegment_046_0243_0060, g32p_row07_traceSegment_046_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 364 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 364 30 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 364 15 15, g32p_row07_traceSegment_046_0364_0015, g32p_row07_traceSegment_046_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 394 15 16, g32p_row07_traceSegment_046_0394_0015, g32p_row07_traceSegment_046_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 364 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 364 30 31, g32p_row07_traceSegment_046_0364_0030, g32p_row07_traceSegment_046_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 425 15 15, g32p_row07_traceSegment_046_0425_0015, g32p_row07_traceSegment_046_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 455 15 16, g32p_row07_traceSegment_046_0455_0015, g32p_row07_traceSegment_046_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 425 30 31, g32p_row07_traceSegment_046_0425_0030, g32p_row07_traceSegment_046_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_046 364 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 364 61 61, g32p_row07_traceSegment_046_0364_0061, g32p_row07_traceSegment_046_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_046 243 243 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 243 121 122, g32p_row07_traceSegment_046_0243_0121, g32p_row07_traceSegment_046_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_046 0 486 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 0 243 243, g32p_row07_traceSegment_046_0000_0243, g32p_row07_traceSegment_046_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 486 15 15, g32p_row07_traceSegment_046_0486_0015, g32p_row07_traceSegment_046_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 516 15 15, g32p_row07_traceSegment_046_0516_0015, g32p_row07_traceSegment_046_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_046 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 486 30 30, g32p_row07_traceSegment_046_0486_0030, g32p_row07_traceSegment_046_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 546 15 15, g32p_row07_traceSegment_046_0546_0015, g32p_row07_traceSegment_046_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 576 15 16, g32p_row07_traceSegment_046_0576_0015, g32p_row07_traceSegment_046_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 546 30 31, g32p_row07_traceSegment_046_0546_0030, g32p_row07_traceSegment_046_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_046 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 486 60 61, g32p_row07_traceSegment_046_0486_0060, g32p_row07_traceSegment_046_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 607 15 15, g32p_row07_traceSegment_046_0607_0015, g32p_row07_traceSegment_046_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 637 15 16, g32p_row07_traceSegment_046_0637_0015, g32p_row07_traceSegment_046_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 607 30 31, g32p_row07_traceSegment_046_0607_0030, g32p_row07_traceSegment_046_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 668 15 15, g32p_row07_traceSegment_046_0668_0015, g32p_row07_traceSegment_046_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 698 15 16, g32p_row07_traceSegment_046_0698_0015, g32p_row07_traceSegment_046_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 668 30 31, g32p_row07_traceSegment_046_0668_0030, g32p_row07_traceSegment_046_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_046 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 607 61 61, g32p_row07_traceSegment_046_0607_0061, g32p_row07_traceSegment_046_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_046 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 486 121 122, g32p_row07_traceSegment_046_0486_0121, g32p_row07_traceSegment_046_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 729 15 15, g32p_row07_traceSegment_046_0729_0015, g32p_row07_traceSegment_046_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 759 15 15, g32p_row07_traceSegment_046_0759_0015, g32p_row07_traceSegment_046_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_046 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 729 30 30, g32p_row07_traceSegment_046_0729_0030, g32p_row07_traceSegment_046_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 789 15 15, g32p_row07_traceSegment_046_0789_0015, g32p_row07_traceSegment_046_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 819 15 16, g32p_row07_traceSegment_046_0819_0015, g32p_row07_traceSegment_046_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 789 30 31, g32p_row07_traceSegment_046_0789_0030, g32p_row07_traceSegment_046_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_046 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 729 60 61, g32p_row07_traceSegment_046_0729_0060, g32p_row07_traceSegment_046_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 850 15 15, g32p_row07_traceSegment_046_0850_0015, g32p_row07_traceSegment_046_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 880 15 16, g32p_row07_traceSegment_046_0880_0015, g32p_row07_traceSegment_046_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 850 30 31, g32p_row07_traceSegment_046_0850_0030, g32p_row07_traceSegment_046_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 911 15 15, g32p_row07_traceSegment_046_0911_0015, g32p_row07_traceSegment_046_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 941 15 16, g32p_row07_traceSegment_046_0941_0015, g32p_row07_traceSegment_046_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 911 30 31, g32p_row07_traceSegment_046_0911_0030, g32p_row07_traceSegment_046_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_046 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 850 61 61, g32p_row07_traceSegment_046_0850_0061, g32p_row07_traceSegment_046_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_046 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 729 121 122, g32p_row07_traceSegment_046_0729_0121, g32p_row07_traceSegment_046_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_046 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 486 243 243, g32p_row07_traceSegment_046_0486_0243, g32p_row07_traceSegment_046_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_046 0 972 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 0 486 486, g32p_row07_traceSegment_046_0000_0486, g32p_row07_traceSegment_046_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 972 15 15, g32p_row07_traceSegment_046_0972_0015, g32p_row07_traceSegment_046_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1002 15 15, g32p_row07_traceSegment_046_1002_0015, g32p_row07_traceSegment_046_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_046 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 972 30 30, g32p_row07_traceSegment_046_0972_0030, g32p_row07_traceSegment_046_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1032 15 15, g32p_row07_traceSegment_046_1032_0015, g32p_row07_traceSegment_046_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1062 15 16, g32p_row07_traceSegment_046_1062_0015, g32p_row07_traceSegment_046_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1032 30 31, g32p_row07_traceSegment_046_1032_0030, g32p_row07_traceSegment_046_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_046 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 972 60 61, g32p_row07_traceSegment_046_0972_0060, g32p_row07_traceSegment_046_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1093 15 15, g32p_row07_traceSegment_046_1093_0015, g32p_row07_traceSegment_046_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1123 15 16, g32p_row07_traceSegment_046_1123_0015, g32p_row07_traceSegment_046_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1093 30 31, g32p_row07_traceSegment_046_1093_0030, g32p_row07_traceSegment_046_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1154 15 15, g32p_row07_traceSegment_046_1154_0015, g32p_row07_traceSegment_046_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1184 15 16, g32p_row07_traceSegment_046_1184_0015, g32p_row07_traceSegment_046_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1154 30 31, g32p_row07_traceSegment_046_1154_0030, g32p_row07_traceSegment_046_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_046 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1093 61 61, g32p_row07_traceSegment_046_1093_0061, g32p_row07_traceSegment_046_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_046 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 972 121 122, g32p_row07_traceSegment_046_0972_0121, g32p_row07_traceSegment_046_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1215 15 15, g32p_row07_traceSegment_046_1215_0015, g32p_row07_traceSegment_046_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1245 15 15, g32p_row07_traceSegment_046_1245_0015, g32p_row07_traceSegment_046_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_046 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1215 30 30, g32p_row07_traceSegment_046_1215_0030, g32p_row07_traceSegment_046_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1290 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1275 30 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1275 15 15, g32p_row07_traceSegment_046_1275_0015, g32p_row07_traceSegment_046_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1305 15 16, g32p_row07_traceSegment_046_1305_0015, g32p_row07_traceSegment_046_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1275 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1275 30 31, g32p_row07_traceSegment_046_1275_0030, g32p_row07_traceSegment_046_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_046 1215 121 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1215 60 61, g32p_row07_traceSegment_046_1215_0060, g32p_row07_traceSegment_046_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1336 15 15, g32p_row07_traceSegment_046_1336_0015, g32p_row07_traceSegment_046_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1381 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1366 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1366 15 16, g32p_row07_traceSegment_046_1366_0015, g32p_row07_traceSegment_046_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1336 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1336 30 31, g32p_row07_traceSegment_046_1336_0030, g32p_row07_traceSegment_046_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1412 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1397 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1397 15 15, g32p_row07_traceSegment_046_1397_0015, g32p_row07_traceSegment_046_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1427 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1442 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1427 31 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1427 15 16, g32p_row07_traceSegment_046_1427_0015, g32p_row07_traceSegment_046_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1397 61 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1397 30 31, g32p_row07_traceSegment_046_1397_0030, g32p_row07_traceSegment_046_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_046 1336 122 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1336 61 61, g32p_row07_traceSegment_046_1336_0061, g32p_row07_traceSegment_046_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_046 1215 243 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1215 121 122, g32p_row07_traceSegment_046_1215_0121, g32p_row07_traceSegment_046_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_046 972 486 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 972 243 243, g32p_row07_traceSegment_046_0972_0243, g32p_row07_traceSegment_046_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1458 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1473 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1458 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1458 15 15, g32p_row07_traceSegment_046_1458_0015, g32p_row07_traceSegment_046_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1488 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1503 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1488 30 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1488 15 15, g32p_row07_traceSegment_046_1488_0015, g32p_row07_traceSegment_046_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_046 1458 60 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1458 30 30, g32p_row07_traceSegment_046_1458_0030, g32p_row07_traceSegment_046_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1518 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1533 15 = [0, 7] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1518 30 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1518 15 15, g32p_row07_traceSegment_046_1518_0015, g32p_row07_traceSegment_046_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1548 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1563 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1548 31 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1548 15 16, g32p_row07_traceSegment_046_1548_0015, g32p_row07_traceSegment_046_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1518 61 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1518 30 31, g32p_row07_traceSegment_046_1518_0030, g32p_row07_traceSegment_046_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_046 1458 121 = [0, 27] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1458 60 61, g32p_row07_traceSegment_046_1458_0060, g32p_row07_traceSegment_046_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1579 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1594 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1579 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1579 15 15, g32p_row07_traceSegment_046_1579_0015, g32p_row07_traceSegment_046_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1609 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1624 16 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1609 31 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1609 15 16, g32p_row07_traceSegment_046_1609_0015, g32p_row07_traceSegment_046_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1579 61 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1579 30 31, g32p_row07_traceSegment_046_1579_0030, g32p_row07_traceSegment_046_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1640 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1655 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1640 30 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1640 15 15, g32p_row07_traceSegment_046_1640_0015, g32p_row07_traceSegment_046_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1670 15 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1685 16 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1670 31 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1670 15 16, g32p_row07_traceSegment_046_1670_0015, g32p_row07_traceSegment_046_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1640 61 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1640 30 31, g32p_row07_traceSegment_046_1640_0030, g32p_row07_traceSegment_046_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_046 1579 122 = [0, 36] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1579 61 61, g32p_row07_traceSegment_046_1579_0061, g32p_row07_traceSegment_046_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_046 1458 243 = [0, 63] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1458 121 122, g32p_row07_traceSegment_046_1458_0121, g32p_row07_traceSegment_046_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1701 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1701 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1701 15 15, g32p_row07_traceSegment_046_1701_0015, g32p_row07_traceSegment_046_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1731 15 15, g32p_row07_traceSegment_046_1731_0015, g32p_row07_traceSegment_046_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_046 1701 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1701 30 30, g32p_row07_traceSegment_046_1701_0030, g32p_row07_traceSegment_046_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1761 15 15, g32p_row07_traceSegment_046_1761_0015, g32p_row07_traceSegment_046_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1791 15 16, g32p_row07_traceSegment_046_1791_0015, g32p_row07_traceSegment_046_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1761 30 31, g32p_row07_traceSegment_046_1761_0030, g32p_row07_traceSegment_046_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_046 1701 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1701 60 61, g32p_row07_traceSegment_046_1701_0060, g32p_row07_traceSegment_046_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1822 15 15, g32p_row07_traceSegment_046_1822_0015, g32p_row07_traceSegment_046_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1852 15 16, g32p_row07_traceSegment_046_1852_0015, g32p_row07_traceSegment_046_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1822 30 31, g32p_row07_traceSegment_046_1822_0030, g32p_row07_traceSegment_046_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_046 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1883 15 15, g32p_row07_traceSegment_046_1883_0015, g32p_row07_traceSegment_046_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_046 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_046 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_046_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_046 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1913 15 16, g32p_row07_traceSegment_046_1913_0015, g32p_row07_traceSegment_046_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_046 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1883 30 31, g32p_row07_traceSegment_046_1883_0030, g32p_row07_traceSegment_046_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_046 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1822 61 61, g32p_row07_traceSegment_046_1822_0061, g32p_row07_traceSegment_046_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_046 1701 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1701 121 122, g32p_row07_traceSegment_046_1701_0121, g32p_row07_traceSegment_046_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_046_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_046 1458 486 = [0, 65] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 1458 243 243, g32p_row07_traceSegment_046_1458_0243, g32p_row07_traceSegment_046_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_046 972 972 = [0, 77] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 972 486 486, g32p_row07_traceSegment_046_0972_0486, g32p_row07_traceSegment_046_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_046_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_046 0 1944 = [0, 108] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_046 0 972 972, g32p_row07_traceSegment_046_0000_0972, g32p_row07_traceSegment_046_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_046 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 46 = [0, 108] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_046_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_053 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 53 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_053_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 0 15 15, g32p_row07_traceSegment_053_0000_0015, g32p_row07_traceSegment_053_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 30 15 15, g32p_row07_traceSegment_053_0030_0015, g32p_row07_traceSegment_053_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_053 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 0 30 30, g32p_row07_traceSegment_053_0000_0030, g32p_row07_traceSegment_053_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 60 15 15, g32p_row07_traceSegment_053_0060_0015, g32p_row07_traceSegment_053_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 90 15 16, g32p_row07_traceSegment_053_0090_0015, g32p_row07_traceSegment_053_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 60 30 31, g32p_row07_traceSegment_053_0060_0030, g32p_row07_traceSegment_053_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_053 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 0 60 61, g32p_row07_traceSegment_053_0000_0060, g32p_row07_traceSegment_053_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 121 15 15, g32p_row07_traceSegment_053_0121_0015, g32p_row07_traceSegment_053_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 166 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 151 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 151 15 16, g32p_row07_traceSegment_053_0151_0015, g32p_row07_traceSegment_053_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 121 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 121 30 31, g32p_row07_traceSegment_053_0121_0030, g32p_row07_traceSegment_053_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 182 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 197 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 182 30 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 182 15 15, g32p_row07_traceSegment_053_0182_0015, g32p_row07_traceSegment_053_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 212 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 227 16 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 212 31 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 212 15 16, g32p_row07_traceSegment_053_0212_0015, g32p_row07_traceSegment_053_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 182 61 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 182 30 31, g32p_row07_traceSegment_053_0182_0030, g32p_row07_traceSegment_053_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_053 121 122 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 121 61 61, g32p_row07_traceSegment_053_0121_0061, g32p_row07_traceSegment_053_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_053 0 243 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 0 121 122, g32p_row07_traceSegment_053_0000_0121, g32p_row07_traceSegment_053_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 243 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 258 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 243 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 243 15 15, g32p_row07_traceSegment_053_0243_0015, g32p_row07_traceSegment_053_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 273 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 288 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 273 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 273 15 15, g32p_row07_traceSegment_053_0273_0015, g32p_row07_traceSegment_053_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_053 243 60 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 243 30 30, g32p_row07_traceSegment_053_0243_0030, g32p_row07_traceSegment_053_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 303 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 318 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 303 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 303 15 15, g32p_row07_traceSegment_053_0303_0015, g32p_row07_traceSegment_053_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 333 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 333 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 333 15 16, g32p_row07_traceSegment_053_0333_0015, g32p_row07_traceSegment_053_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 303 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 303 30 31, g32p_row07_traceSegment_053_0303_0030, g32p_row07_traceSegment_053_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_053 243 121 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 243 60 61, g32p_row07_traceSegment_053_0243_0060, g32p_row07_traceSegment_053_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 364 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 364 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 364 15 15, g32p_row07_traceSegment_053_0364_0015, g32p_row07_traceSegment_053_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 394 15 16, g32p_row07_traceSegment_053_0394_0015, g32p_row07_traceSegment_053_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 364 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 364 30 31, g32p_row07_traceSegment_053_0364_0030, g32p_row07_traceSegment_053_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 425 15 15, g32p_row07_traceSegment_053_0425_0015, g32p_row07_traceSegment_053_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 455 15 16, g32p_row07_traceSegment_053_0455_0015, g32p_row07_traceSegment_053_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 425 30 31, g32p_row07_traceSegment_053_0425_0030, g32p_row07_traceSegment_053_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_053 364 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 364 61 61, g32p_row07_traceSegment_053_0364_0061, g32p_row07_traceSegment_053_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_053 243 243 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 243 121 122, g32p_row07_traceSegment_053_0243_0121, g32p_row07_traceSegment_053_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_053 0 486 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 0 243 243, g32p_row07_traceSegment_053_0000_0243, g32p_row07_traceSegment_053_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 486 15 15, g32p_row07_traceSegment_053_0486_0015, g32p_row07_traceSegment_053_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 516 15 15, g32p_row07_traceSegment_053_0516_0015, g32p_row07_traceSegment_053_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_053 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 486 30 30, g32p_row07_traceSegment_053_0486_0030, g32p_row07_traceSegment_053_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 546 15 15, g32p_row07_traceSegment_053_0546_0015, g32p_row07_traceSegment_053_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 576 15 16, g32p_row07_traceSegment_053_0576_0015, g32p_row07_traceSegment_053_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 546 30 31, g32p_row07_traceSegment_053_0546_0030, g32p_row07_traceSegment_053_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_053 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 486 60 61, g32p_row07_traceSegment_053_0486_0060, g32p_row07_traceSegment_053_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 607 15 15, g32p_row07_traceSegment_053_0607_0015, g32p_row07_traceSegment_053_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 637 15 16, g32p_row07_traceSegment_053_0637_0015, g32p_row07_traceSegment_053_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 607 30 31, g32p_row07_traceSegment_053_0607_0030, g32p_row07_traceSegment_053_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 668 15 15, g32p_row07_traceSegment_053_0668_0015, g32p_row07_traceSegment_053_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 698 15 16, g32p_row07_traceSegment_053_0698_0015, g32p_row07_traceSegment_053_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 668 30 31, g32p_row07_traceSegment_053_0668_0030, g32p_row07_traceSegment_053_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_053 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 607 61 61, g32p_row07_traceSegment_053_0607_0061, g32p_row07_traceSegment_053_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_053 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 486 121 122, g32p_row07_traceSegment_053_0486_0121, g32p_row07_traceSegment_053_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 729 15 15, g32p_row07_traceSegment_053_0729_0015, g32p_row07_traceSegment_053_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 759 15 15, g32p_row07_traceSegment_053_0759_0015, g32p_row07_traceSegment_053_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_053 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 729 30 30, g32p_row07_traceSegment_053_0729_0030, g32p_row07_traceSegment_053_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 789 15 15, g32p_row07_traceSegment_053_0789_0015, g32p_row07_traceSegment_053_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 819 15 16, g32p_row07_traceSegment_053_0819_0015, g32p_row07_traceSegment_053_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 789 30 31, g32p_row07_traceSegment_053_0789_0030, g32p_row07_traceSegment_053_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_053 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 729 60 61, g32p_row07_traceSegment_053_0729_0060, g32p_row07_traceSegment_053_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 850 15 15, g32p_row07_traceSegment_053_0850_0015, g32p_row07_traceSegment_053_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 880 15 16, g32p_row07_traceSegment_053_0880_0015, g32p_row07_traceSegment_053_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 850 30 31, g32p_row07_traceSegment_053_0850_0030, g32p_row07_traceSegment_053_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 911 15 15, g32p_row07_traceSegment_053_0911_0015, g32p_row07_traceSegment_053_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 941 15 16, g32p_row07_traceSegment_053_0941_0015, g32p_row07_traceSegment_053_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 911 30 31, g32p_row07_traceSegment_053_0911_0030, g32p_row07_traceSegment_053_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_053 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 850 61 61, g32p_row07_traceSegment_053_0850_0061, g32p_row07_traceSegment_053_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_053 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 729 121 122, g32p_row07_traceSegment_053_0729_0121, g32p_row07_traceSegment_053_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_053 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 486 243 243, g32p_row07_traceSegment_053_0486_0243, g32p_row07_traceSegment_053_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_053 0 972 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 0 486 486, g32p_row07_traceSegment_053_0000_0486, g32p_row07_traceSegment_053_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 972 15 15, g32p_row07_traceSegment_053_0972_0015, g32p_row07_traceSegment_053_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1002 15 15, g32p_row07_traceSegment_053_1002_0015, g32p_row07_traceSegment_053_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_053 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 972 30 30, g32p_row07_traceSegment_053_0972_0030, g32p_row07_traceSegment_053_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1032 15 15, g32p_row07_traceSegment_053_1032_0015, g32p_row07_traceSegment_053_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1062 15 16, g32p_row07_traceSegment_053_1062_0015, g32p_row07_traceSegment_053_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1032 30 31, g32p_row07_traceSegment_053_1032_0030, g32p_row07_traceSegment_053_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_053 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 972 60 61, g32p_row07_traceSegment_053_0972_0060, g32p_row07_traceSegment_053_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1093 15 15, g32p_row07_traceSegment_053_1093_0015, g32p_row07_traceSegment_053_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1123 15 16, g32p_row07_traceSegment_053_1123_0015, g32p_row07_traceSegment_053_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1093 30 31, g32p_row07_traceSegment_053_1093_0030, g32p_row07_traceSegment_053_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1154 15 15, g32p_row07_traceSegment_053_1154_0015, g32p_row07_traceSegment_053_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1184 15 16, g32p_row07_traceSegment_053_1184_0015, g32p_row07_traceSegment_053_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1154 30 31, g32p_row07_traceSegment_053_1154_0030, g32p_row07_traceSegment_053_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_053 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1093 61 61, g32p_row07_traceSegment_053_1093_0061, g32p_row07_traceSegment_053_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_053 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 972 121 122, g32p_row07_traceSegment_053_0972_0121, g32p_row07_traceSegment_053_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1215 15 15, g32p_row07_traceSegment_053_1215_0015, g32p_row07_traceSegment_053_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1245 15 15, g32p_row07_traceSegment_053_1245_0015, g32p_row07_traceSegment_053_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_053 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1215 30 30, g32p_row07_traceSegment_053_1215_0030, g32p_row07_traceSegment_053_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1290 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1275 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1275 15 15, g32p_row07_traceSegment_053_1275_0015, g32p_row07_traceSegment_053_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1305 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1320 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1305 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1305 15 16, g32p_row07_traceSegment_053_1305_0015, g32p_row07_traceSegment_053_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1275 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1275 30 31, g32p_row07_traceSegment_053_1275_0030, g32p_row07_traceSegment_053_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_053 1215 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1215 60 61, g32p_row07_traceSegment_053_1215_0060, g32p_row07_traceSegment_053_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1351 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1336 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1336 15 15, g32p_row07_traceSegment_053_1336_0015, g32p_row07_traceSegment_053_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1366 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1381 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1366 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1366 15 16, g32p_row07_traceSegment_053_1366_0015, g32p_row07_traceSegment_053_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1336 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1336 30 31, g32p_row07_traceSegment_053_1336_0030, g32p_row07_traceSegment_053_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1397 15 15, g32p_row07_traceSegment_053_1397_0015, g32p_row07_traceSegment_053_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1442 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1427 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1427 15 16, g32p_row07_traceSegment_053_1427_0015, g32p_row07_traceSegment_053_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1397 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1397 30 31, g32p_row07_traceSegment_053_1397_0030, g32p_row07_traceSegment_053_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_053 1336 122 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1336 61 61, g32p_row07_traceSegment_053_1336_0061, g32p_row07_traceSegment_053_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_053 1215 243 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1215 121 122, g32p_row07_traceSegment_053_1215_0121, g32p_row07_traceSegment_053_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_053 972 486 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 972 243 243, g32p_row07_traceSegment_053_0972_0243, g32p_row07_traceSegment_053_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1458 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1473 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1458 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1458 15 15, g32p_row07_traceSegment_053_1458_0015, g32p_row07_traceSegment_053_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1503 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1488 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1488 15 15, g32p_row07_traceSegment_053_1488_0015, g32p_row07_traceSegment_053_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_053 1458 60 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1458 30 30, g32p_row07_traceSegment_053_1458_0030, g32p_row07_traceSegment_053_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1518 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1533 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1518 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1518 15 15, g32p_row07_traceSegment_053_1518_0015, g32p_row07_traceSegment_053_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1548 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1563 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1548 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1548 15 16, g32p_row07_traceSegment_053_1548_0015, g32p_row07_traceSegment_053_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1518 61 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1518 30 31, g32p_row07_traceSegment_053_1518_0030, g32p_row07_traceSegment_053_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_053 1458 121 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1458 60 61, g32p_row07_traceSegment_053_1458_0060, g32p_row07_traceSegment_053_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1579 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1594 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1579 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1579 15 15, g32p_row07_traceSegment_053_1579_0015, g32p_row07_traceSegment_053_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1609 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1624 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1609 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1609 15 16, g32p_row07_traceSegment_053_1609_0015, g32p_row07_traceSegment_053_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1579 61 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1579 30 31, g32p_row07_traceSegment_053_1579_0030, g32p_row07_traceSegment_053_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1640 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1655 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1640 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1640 15 15, g32p_row07_traceSegment_053_1640_0015, g32p_row07_traceSegment_053_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1670 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1685 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1670 31 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1670 15 16, g32p_row07_traceSegment_053_1670_0015, g32p_row07_traceSegment_053_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1640 61 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1640 30 31, g32p_row07_traceSegment_053_1640_0030, g32p_row07_traceSegment_053_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_053 1579 122 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1579 61 61, g32p_row07_traceSegment_053_1579_0061, g32p_row07_traceSegment_053_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_053 1458 243 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1458 121 122, g32p_row07_traceSegment_053_1458_0121, g32p_row07_traceSegment_053_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1701 15 15, g32p_row07_traceSegment_053_1701_0015, g32p_row07_traceSegment_053_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1731 15 15, g32p_row07_traceSegment_053_1731_0015, g32p_row07_traceSegment_053_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_053 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1701 30 30, g32p_row07_traceSegment_053_1701_0030, g32p_row07_traceSegment_053_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1761 15 15, g32p_row07_traceSegment_053_1761_0015, g32p_row07_traceSegment_053_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1791 15 16, g32p_row07_traceSegment_053_1791_0015, g32p_row07_traceSegment_053_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1761 30 31, g32p_row07_traceSegment_053_1761_0030, g32p_row07_traceSegment_053_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_053 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1701 60 61, g32p_row07_traceSegment_053_1701_0060, g32p_row07_traceSegment_053_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1822 15 15, g32p_row07_traceSegment_053_1822_0015, g32p_row07_traceSegment_053_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1852 15 16, g32p_row07_traceSegment_053_1852_0015, g32p_row07_traceSegment_053_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1822 30 31, g32p_row07_traceSegment_053_1822_0030, g32p_row07_traceSegment_053_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_053 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1883 15 15, g32p_row07_traceSegment_053_1883_0015, g32p_row07_traceSegment_053_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_053 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_053 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_053_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_053 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1913 15 16, g32p_row07_traceSegment_053_1913_0015, g32p_row07_traceSegment_053_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_053 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1883 30 31, g32p_row07_traceSegment_053_1883_0030, g32p_row07_traceSegment_053_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_053 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1822 61 61, g32p_row07_traceSegment_053_1822_0061, g32p_row07_traceSegment_053_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_053 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1701 121 122, g32p_row07_traceSegment_053_1701_0121, g32p_row07_traceSegment_053_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_053_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_053 1458 486 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 1458 243 243, g32p_row07_traceSegment_053_1458_0243, g32p_row07_traceSegment_053_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_053 972 972 = [0, 41] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 972 486 486, g32p_row07_traceSegment_053_0972_0486, g32p_row07_traceSegment_053_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_053_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_053 0 1944 = [0, 72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_053 0 972 972, g32p_row07_traceSegment_053_0000_0972, g32p_row07_traceSegment_053_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_053 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 53 = [0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_053_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_054 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 54 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_054_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 0 15 15, g32p_row07_traceSegment_054_0000_0015, g32p_row07_traceSegment_054_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 30 15 15, g32p_row07_traceSegment_054_0030_0015, g32p_row07_traceSegment_054_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_054 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 0 30 30, g32p_row07_traceSegment_054_0000_0030, g32p_row07_traceSegment_054_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 60 15 15, g32p_row07_traceSegment_054_0060_0015, g32p_row07_traceSegment_054_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 90 15 16, g32p_row07_traceSegment_054_0090_0015, g32p_row07_traceSegment_054_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 60 30 31, g32p_row07_traceSegment_054_0060_0030, g32p_row07_traceSegment_054_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_054 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 0 60 61, g32p_row07_traceSegment_054_0000_0060, g32p_row07_traceSegment_054_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 121 15 15, g32p_row07_traceSegment_054_0121_0015, g32p_row07_traceSegment_054_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 151 15 16, g32p_row07_traceSegment_054_0151_0015, g32p_row07_traceSegment_054_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 121 30 31, g32p_row07_traceSegment_054_0121_0030, g32p_row07_traceSegment_054_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 197 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 182 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 182 15 15, g32p_row07_traceSegment_054_0182_0015, g32p_row07_traceSegment_054_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 212 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 227 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 212 31 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 212 15 16, g32p_row07_traceSegment_054_0212_0015, g32p_row07_traceSegment_054_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 182 61 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 182 30 31, g32p_row07_traceSegment_054_0182_0030, g32p_row07_traceSegment_054_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_054 121 122 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 121 61 61, g32p_row07_traceSegment_054_0121_0061, g32p_row07_traceSegment_054_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_054 0 243 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 0 121 122, g32p_row07_traceSegment_054_0000_0121, g32p_row07_traceSegment_054_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 258 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 243 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 243 15 15, g32p_row07_traceSegment_054_0243_0015, g32p_row07_traceSegment_054_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 273 15 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 288 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 273 30 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 273 15 15, g32p_row07_traceSegment_054_0273_0015, g32p_row07_traceSegment_054_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_054 243 60 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 243 30 30, g32p_row07_traceSegment_054_0243_0030, g32p_row07_traceSegment_054_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 303 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 318 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 303 30 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 303 15 15, g32p_row07_traceSegment_054_0303_0015, g32p_row07_traceSegment_054_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 333 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 348 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 333 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 333 15 16, g32p_row07_traceSegment_054_0333_0015, g32p_row07_traceSegment_054_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 303 61 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 303 30 31, g32p_row07_traceSegment_054_0303_0030, g32p_row07_traceSegment_054_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_054 243 121 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 243 60 61, g32p_row07_traceSegment_054_0243_0060, g32p_row07_traceSegment_054_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 364 15 15, g32p_row07_traceSegment_054_0364_0015, g32p_row07_traceSegment_054_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 394 15 16, g32p_row07_traceSegment_054_0394_0015, g32p_row07_traceSegment_054_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 364 30 31, g32p_row07_traceSegment_054_0364_0030, g32p_row07_traceSegment_054_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 425 15 15, g32p_row07_traceSegment_054_0425_0015, g32p_row07_traceSegment_054_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 455 15 16, g32p_row07_traceSegment_054_0455_0015, g32p_row07_traceSegment_054_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 425 30 31, g32p_row07_traceSegment_054_0425_0030, g32p_row07_traceSegment_054_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_054 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 364 61 61, g32p_row07_traceSegment_054_0364_0061, g32p_row07_traceSegment_054_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_054 243 243 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 243 121 122, g32p_row07_traceSegment_054_0243_0121, g32p_row07_traceSegment_054_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_054 0 486 = [0, 25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 0 243 243, g32p_row07_traceSegment_054_0000_0243, g32p_row07_traceSegment_054_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 486 15 15, g32p_row07_traceSegment_054_0486_0015, g32p_row07_traceSegment_054_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 516 15 15, g32p_row07_traceSegment_054_0516_0015, g32p_row07_traceSegment_054_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_054 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 486 30 30, g32p_row07_traceSegment_054_0486_0030, g32p_row07_traceSegment_054_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 546 15 15, g32p_row07_traceSegment_054_0546_0015, g32p_row07_traceSegment_054_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 576 15 16, g32p_row07_traceSegment_054_0576_0015, g32p_row07_traceSegment_054_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 546 30 31, g32p_row07_traceSegment_054_0546_0030, g32p_row07_traceSegment_054_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_054 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 486 60 61, g32p_row07_traceSegment_054_0486_0060, g32p_row07_traceSegment_054_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 607 15 15, g32p_row07_traceSegment_054_0607_0015, g32p_row07_traceSegment_054_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 637 15 16, g32p_row07_traceSegment_054_0637_0015, g32p_row07_traceSegment_054_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 607 30 31, g32p_row07_traceSegment_054_0607_0030, g32p_row07_traceSegment_054_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 668 15 15, g32p_row07_traceSegment_054_0668_0015, g32p_row07_traceSegment_054_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 698 15 16, g32p_row07_traceSegment_054_0698_0015, g32p_row07_traceSegment_054_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 668 30 31, g32p_row07_traceSegment_054_0668_0030, g32p_row07_traceSegment_054_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_054 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 607 61 61, g32p_row07_traceSegment_054_0607_0061, g32p_row07_traceSegment_054_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_054 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 486 121 122, g32p_row07_traceSegment_054_0486_0121, g32p_row07_traceSegment_054_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 729 15 15, g32p_row07_traceSegment_054_0729_0015, g32p_row07_traceSegment_054_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 759 15 15, g32p_row07_traceSegment_054_0759_0015, g32p_row07_traceSegment_054_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_054 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 729 30 30, g32p_row07_traceSegment_054_0729_0030, g32p_row07_traceSegment_054_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 789 15 15, g32p_row07_traceSegment_054_0789_0015, g32p_row07_traceSegment_054_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 819 15 16, g32p_row07_traceSegment_054_0819_0015, g32p_row07_traceSegment_054_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 789 30 31, g32p_row07_traceSegment_054_0789_0030, g32p_row07_traceSegment_054_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_054 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 729 60 61, g32p_row07_traceSegment_054_0729_0060, g32p_row07_traceSegment_054_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 850 15 15, g32p_row07_traceSegment_054_0850_0015, g32p_row07_traceSegment_054_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 880 15 16, g32p_row07_traceSegment_054_0880_0015, g32p_row07_traceSegment_054_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 850 30 31, g32p_row07_traceSegment_054_0850_0030, g32p_row07_traceSegment_054_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 911 15 15, g32p_row07_traceSegment_054_0911_0015, g32p_row07_traceSegment_054_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 941 15 16, g32p_row07_traceSegment_054_0941_0015, g32p_row07_traceSegment_054_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 911 30 31, g32p_row07_traceSegment_054_0911_0030, g32p_row07_traceSegment_054_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_054 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 850 61 61, g32p_row07_traceSegment_054_0850_0061, g32p_row07_traceSegment_054_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_054 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 729 121 122, g32p_row07_traceSegment_054_0729_0121, g32p_row07_traceSegment_054_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_054 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 486 243 243, g32p_row07_traceSegment_054_0486_0243, g32p_row07_traceSegment_054_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_054 0 972 = [0, 25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 0 486 486, g32p_row07_traceSegment_054_0000_0486, g32p_row07_traceSegment_054_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 972 15 15, g32p_row07_traceSegment_054_0972_0015, g32p_row07_traceSegment_054_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1002 15 15, g32p_row07_traceSegment_054_1002_0015, g32p_row07_traceSegment_054_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_054 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 972 30 30, g32p_row07_traceSegment_054_0972_0030, g32p_row07_traceSegment_054_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1032 15 15, g32p_row07_traceSegment_054_1032_0015, g32p_row07_traceSegment_054_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1062 15 16, g32p_row07_traceSegment_054_1062_0015, g32p_row07_traceSegment_054_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1032 30 31, g32p_row07_traceSegment_054_1032_0030, g32p_row07_traceSegment_054_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_054 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 972 60 61, g32p_row07_traceSegment_054_0972_0060, g32p_row07_traceSegment_054_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1093 15 15, g32p_row07_traceSegment_054_1093_0015, g32p_row07_traceSegment_054_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1123 15 16, g32p_row07_traceSegment_054_1123_0015, g32p_row07_traceSegment_054_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1093 30 31, g32p_row07_traceSegment_054_1093_0030, g32p_row07_traceSegment_054_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1154 15 15, g32p_row07_traceSegment_054_1154_0015, g32p_row07_traceSegment_054_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1184 15 16, g32p_row07_traceSegment_054_1184_0015, g32p_row07_traceSegment_054_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1154 30 31, g32p_row07_traceSegment_054_1154_0030, g32p_row07_traceSegment_054_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_054 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1093 61 61, g32p_row07_traceSegment_054_1093_0061, g32p_row07_traceSegment_054_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_054 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 972 121 122, g32p_row07_traceSegment_054_0972_0121, g32p_row07_traceSegment_054_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1215 15 15, g32p_row07_traceSegment_054_1215_0015, g32p_row07_traceSegment_054_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1245 15 15, g32p_row07_traceSegment_054_1245_0015, g32p_row07_traceSegment_054_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_054 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1215 30 30, g32p_row07_traceSegment_054_1215_0030, g32p_row07_traceSegment_054_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1275 15 15, g32p_row07_traceSegment_054_1275_0015, g32p_row07_traceSegment_054_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1305 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1320 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1305 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1305 15 16, g32p_row07_traceSegment_054_1305_0015, g32p_row07_traceSegment_054_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1275 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1275 30 31, g32p_row07_traceSegment_054_1275_0030, g32p_row07_traceSegment_054_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_054 1215 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1215 60 61, g32p_row07_traceSegment_054_1215_0060, g32p_row07_traceSegment_054_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1336 15 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1351 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1336 30 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1336 15 15, g32p_row07_traceSegment_054_1336_0015, g32p_row07_traceSegment_054_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1366 15 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1381 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1366 31 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1366 15 16, g32p_row07_traceSegment_054_1366_0015, g32p_row07_traceSegment_054_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1336 61 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1336 30 31, g32p_row07_traceSegment_054_1336_0030, g32p_row07_traceSegment_054_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1397 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1412 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1397 30 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1397 15 15, g32p_row07_traceSegment_054_1397_0015, g32p_row07_traceSegment_054_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1427 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1442 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1427 31 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1427 15 16, g32p_row07_traceSegment_054_1427_0015, g32p_row07_traceSegment_054_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1397 61 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1397 30 31, g32p_row07_traceSegment_054_1397_0030, g32p_row07_traceSegment_054_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_054 1336 122 = [0, 29] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1336 61 61, g32p_row07_traceSegment_054_1336_0061, g32p_row07_traceSegment_054_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_054 1215 243 = [0, 32] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1215 121 122, g32p_row07_traceSegment_054_1215_0121, g32p_row07_traceSegment_054_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_054 972 486 = [0, 32] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 972 243 243, g32p_row07_traceSegment_054_0972_0243, g32p_row07_traceSegment_054_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1458 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1473 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1458 30 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1458 15 15, g32p_row07_traceSegment_054_1458_0015, g32p_row07_traceSegment_054_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1488 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1503 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1488 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1488 15 15, g32p_row07_traceSegment_054_1488_0015, g32p_row07_traceSegment_054_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_054 1458 60 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1458 30 30, g32p_row07_traceSegment_054_1458_0030, g32p_row07_traceSegment_054_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1518 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1518 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1518 15 15, g32p_row07_traceSegment_054_1518_0015, g32p_row07_traceSegment_054_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1548 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1548 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1548 15 16, g32p_row07_traceSegment_054_1548_0015, g32p_row07_traceSegment_054_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1518 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1518 30 31, g32p_row07_traceSegment_054_1518_0030, g32p_row07_traceSegment_054_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_054 1458 121 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1458 60 61, g32p_row07_traceSegment_054_1458_0060, g32p_row07_traceSegment_054_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1594 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1579 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1579 15 15, g32p_row07_traceSegment_054_1579_0015, g32p_row07_traceSegment_054_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1609 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1609 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1609 15 16, g32p_row07_traceSegment_054_1609_0015, g32p_row07_traceSegment_054_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1579 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1579 30 31, g32p_row07_traceSegment_054_1579_0030, g32p_row07_traceSegment_054_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1655 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1640 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1640 15 15, g32p_row07_traceSegment_054_1640_0015, g32p_row07_traceSegment_054_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1670 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1670 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1670 15 16, g32p_row07_traceSegment_054_1670_0015, g32p_row07_traceSegment_054_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1640 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1640 30 31, g32p_row07_traceSegment_054_1640_0030, g32p_row07_traceSegment_054_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_054 1579 122 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1579 61 61, g32p_row07_traceSegment_054_1579_0061, g32p_row07_traceSegment_054_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_054 1458 243 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1458 121 122, g32p_row07_traceSegment_054_1458_0121, g32p_row07_traceSegment_054_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1701 15 15, g32p_row07_traceSegment_054_1701_0015, g32p_row07_traceSegment_054_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1731 15 15, g32p_row07_traceSegment_054_1731_0015, g32p_row07_traceSegment_054_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_054 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1701 30 30, g32p_row07_traceSegment_054_1701_0030, g32p_row07_traceSegment_054_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1761 15 15, g32p_row07_traceSegment_054_1761_0015, g32p_row07_traceSegment_054_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1791 15 16, g32p_row07_traceSegment_054_1791_0015, g32p_row07_traceSegment_054_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1761 30 31, g32p_row07_traceSegment_054_1761_0030, g32p_row07_traceSegment_054_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_054 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1701 60 61, g32p_row07_traceSegment_054_1701_0060, g32p_row07_traceSegment_054_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1822 15 15, g32p_row07_traceSegment_054_1822_0015, g32p_row07_traceSegment_054_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1852 15 16, g32p_row07_traceSegment_054_1852_0015, g32p_row07_traceSegment_054_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1822 30 31, g32p_row07_traceSegment_054_1822_0030, g32p_row07_traceSegment_054_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_054 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1883 15 15, g32p_row07_traceSegment_054_1883_0015, g32p_row07_traceSegment_054_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_054 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_054 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_054_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_054 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1913 15 16, g32p_row07_traceSegment_054_1913_0015, g32p_row07_traceSegment_054_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_054 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1883 30 31, g32p_row07_traceSegment_054_1883_0030, g32p_row07_traceSegment_054_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_054 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1822 61 61, g32p_row07_traceSegment_054_1822_0061, g32p_row07_traceSegment_054_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_054 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1701 121 122, g32p_row07_traceSegment_054_1701_0121, g32p_row07_traceSegment_054_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_054_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_054 1458 486 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 1458 243 243, g32p_row07_traceSegment_054_1458_0243, g32p_row07_traceSegment_054_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_054 972 972 = [0, 47] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 972 486 486, g32p_row07_traceSegment_054_0972_0486, g32p_row07_traceSegment_054_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_054_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_054 0 1944 = [0, 72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_054 0 972 972, g32p_row07_traceSegment_054_0000_0972, g32p_row07_traceSegment_054_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_054 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 54 = [0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_054_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_056 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 56 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_056_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 0 15 15, g32p_row07_traceSegment_056_0000_0015, g32p_row07_traceSegment_056_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 30 15 15, g32p_row07_traceSegment_056_0030_0015, g32p_row07_traceSegment_056_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_056 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 0 30 30, g32p_row07_traceSegment_056_0000_0030, g32p_row07_traceSegment_056_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 60 15 15, g32p_row07_traceSegment_056_0060_0015, g32p_row07_traceSegment_056_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 90 15 16, g32p_row07_traceSegment_056_0090_0015, g32p_row07_traceSegment_056_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 60 30 31, g32p_row07_traceSegment_056_0060_0030, g32p_row07_traceSegment_056_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_056 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 0 60 61, g32p_row07_traceSegment_056_0000_0060, g32p_row07_traceSegment_056_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 121 15 15, g32p_row07_traceSegment_056_0121_0015, g32p_row07_traceSegment_056_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 166 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 151 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 151 15 16, g32p_row07_traceSegment_056_0151_0015, g32p_row07_traceSegment_056_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 121 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 121 30 31, g32p_row07_traceSegment_056_0121_0030, g32p_row07_traceSegment_056_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 197 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 182 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 182 15 15, g32p_row07_traceSegment_056_0182_0015, g32p_row07_traceSegment_056_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 212 15 16, g32p_row07_traceSegment_056_0212_0015, g32p_row07_traceSegment_056_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 182 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 182 30 31, g32p_row07_traceSegment_056_0182_0030, g32p_row07_traceSegment_056_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_056 121 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 121 61 61, g32p_row07_traceSegment_056_0121_0061, g32p_row07_traceSegment_056_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_056 0 243 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 0 121 122, g32p_row07_traceSegment_056_0000_0121, g32p_row07_traceSegment_056_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 243 15 15, g32p_row07_traceSegment_056_0243_0015, g32p_row07_traceSegment_056_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 273 15 15, g32p_row07_traceSegment_056_0273_0015, g32p_row07_traceSegment_056_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_056 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 243 30 30, g32p_row07_traceSegment_056_0243_0030, g32p_row07_traceSegment_056_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 303 15 15, g32p_row07_traceSegment_056_0303_0015, g32p_row07_traceSegment_056_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 333 15 16, g32p_row07_traceSegment_056_0333_0015, g32p_row07_traceSegment_056_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 303 30 31, g32p_row07_traceSegment_056_0303_0030, g32p_row07_traceSegment_056_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_056 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 243 60 61, g32p_row07_traceSegment_056_0243_0060, g32p_row07_traceSegment_056_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 364 15 15, g32p_row07_traceSegment_056_0364_0015, g32p_row07_traceSegment_056_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 394 15 16, g32p_row07_traceSegment_056_0394_0015, g32p_row07_traceSegment_056_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 364 30 31, g32p_row07_traceSegment_056_0364_0030, g32p_row07_traceSegment_056_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 425 15 15, g32p_row07_traceSegment_056_0425_0015, g32p_row07_traceSegment_056_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 455 15 16, g32p_row07_traceSegment_056_0455_0015, g32p_row07_traceSegment_056_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 425 30 31, g32p_row07_traceSegment_056_0425_0030, g32p_row07_traceSegment_056_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_056 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 364 61 61, g32p_row07_traceSegment_056_0364_0061, g32p_row07_traceSegment_056_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_056 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 243 121 122, g32p_row07_traceSegment_056_0243_0121, g32p_row07_traceSegment_056_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_056 0 486 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 0 243 243, g32p_row07_traceSegment_056_0000_0243, g32p_row07_traceSegment_056_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 486 15 15, g32p_row07_traceSegment_056_0486_0015, g32p_row07_traceSegment_056_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 516 15 15, g32p_row07_traceSegment_056_0516_0015, g32p_row07_traceSegment_056_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_056 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 486 30 30, g32p_row07_traceSegment_056_0486_0030, g32p_row07_traceSegment_056_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 546 15 15, g32p_row07_traceSegment_056_0546_0015, g32p_row07_traceSegment_056_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 576 15 16, g32p_row07_traceSegment_056_0576_0015, g32p_row07_traceSegment_056_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 546 30 31, g32p_row07_traceSegment_056_0546_0030, g32p_row07_traceSegment_056_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_056 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 486 60 61, g32p_row07_traceSegment_056_0486_0060, g32p_row07_traceSegment_056_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 607 15 15, g32p_row07_traceSegment_056_0607_0015, g32p_row07_traceSegment_056_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 637 15 16, g32p_row07_traceSegment_056_0637_0015, g32p_row07_traceSegment_056_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 607 30 31, g32p_row07_traceSegment_056_0607_0030, g32p_row07_traceSegment_056_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 668 15 15, g32p_row07_traceSegment_056_0668_0015, g32p_row07_traceSegment_056_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 698 15 16, g32p_row07_traceSegment_056_0698_0015, g32p_row07_traceSegment_056_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 668 30 31, g32p_row07_traceSegment_056_0668_0030, g32p_row07_traceSegment_056_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_056 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 607 61 61, g32p_row07_traceSegment_056_0607_0061, g32p_row07_traceSegment_056_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_056 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 486 121 122, g32p_row07_traceSegment_056_0486_0121, g32p_row07_traceSegment_056_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 729 15 15, g32p_row07_traceSegment_056_0729_0015, g32p_row07_traceSegment_056_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 759 15 15, g32p_row07_traceSegment_056_0759_0015, g32p_row07_traceSegment_056_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_056 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 729 30 30, g32p_row07_traceSegment_056_0729_0030, g32p_row07_traceSegment_056_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 789 15 15, g32p_row07_traceSegment_056_0789_0015, g32p_row07_traceSegment_056_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 819 15 16, g32p_row07_traceSegment_056_0819_0015, g32p_row07_traceSegment_056_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 789 30 31, g32p_row07_traceSegment_056_0789_0030, g32p_row07_traceSegment_056_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_056 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 729 60 61, g32p_row07_traceSegment_056_0729_0060, g32p_row07_traceSegment_056_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 850 15 15, g32p_row07_traceSegment_056_0850_0015, g32p_row07_traceSegment_056_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 880 15 16, g32p_row07_traceSegment_056_0880_0015, g32p_row07_traceSegment_056_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 850 30 31, g32p_row07_traceSegment_056_0850_0030, g32p_row07_traceSegment_056_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 911 15 15, g32p_row07_traceSegment_056_0911_0015, g32p_row07_traceSegment_056_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 941 15 16, g32p_row07_traceSegment_056_0941_0015, g32p_row07_traceSegment_056_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 911 30 31, g32p_row07_traceSegment_056_0911_0030, g32p_row07_traceSegment_056_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_056 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 850 61 61, g32p_row07_traceSegment_056_0850_0061, g32p_row07_traceSegment_056_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_056 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 729 121 122, g32p_row07_traceSegment_056_0729_0121, g32p_row07_traceSegment_056_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_056 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 486 243 243, g32p_row07_traceSegment_056_0486_0243, g32p_row07_traceSegment_056_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_056 0 972 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 0 486 486, g32p_row07_traceSegment_056_0000_0486, g32p_row07_traceSegment_056_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 972 15 15, g32p_row07_traceSegment_056_0972_0015, g32p_row07_traceSegment_056_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1002 15 15, g32p_row07_traceSegment_056_1002_0015, g32p_row07_traceSegment_056_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_056 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 972 30 30, g32p_row07_traceSegment_056_0972_0030, g32p_row07_traceSegment_056_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1032 15 15, g32p_row07_traceSegment_056_1032_0015, g32p_row07_traceSegment_056_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1062 15 16, g32p_row07_traceSegment_056_1062_0015, g32p_row07_traceSegment_056_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1032 30 31, g32p_row07_traceSegment_056_1032_0030, g32p_row07_traceSegment_056_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_056 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 972 60 61, g32p_row07_traceSegment_056_0972_0060, g32p_row07_traceSegment_056_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1093 15 15, g32p_row07_traceSegment_056_1093_0015, g32p_row07_traceSegment_056_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1123 15 16, g32p_row07_traceSegment_056_1123_0015, g32p_row07_traceSegment_056_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1093 30 31, g32p_row07_traceSegment_056_1093_0030, g32p_row07_traceSegment_056_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1154 15 15, g32p_row07_traceSegment_056_1154_0015, g32p_row07_traceSegment_056_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1184 15 16, g32p_row07_traceSegment_056_1184_0015, g32p_row07_traceSegment_056_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1154 30 31, g32p_row07_traceSegment_056_1154_0030, g32p_row07_traceSegment_056_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_056 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1093 61 61, g32p_row07_traceSegment_056_1093_0061, g32p_row07_traceSegment_056_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_056 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 972 121 122, g32p_row07_traceSegment_056_0972_0121, g32p_row07_traceSegment_056_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1215 15 15, g32p_row07_traceSegment_056_1215_0015, g32p_row07_traceSegment_056_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1245 15 15, g32p_row07_traceSegment_056_1245_0015, g32p_row07_traceSegment_056_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_056 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1215 30 30, g32p_row07_traceSegment_056_1215_0030, g32p_row07_traceSegment_056_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1290 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1275 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1275 15 15, g32p_row07_traceSegment_056_1275_0015, g32p_row07_traceSegment_056_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1305 15 16, g32p_row07_traceSegment_056_1305_0015, g32p_row07_traceSegment_056_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1275 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1275 30 31, g32p_row07_traceSegment_056_1275_0030, g32p_row07_traceSegment_056_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_056 1215 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1215 60 61, g32p_row07_traceSegment_056_1215_0060, g32p_row07_traceSegment_056_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1336 15 15, g32p_row07_traceSegment_056_1336_0015, g32p_row07_traceSegment_056_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1366 15 16, g32p_row07_traceSegment_056_1366_0015, g32p_row07_traceSegment_056_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1336 30 31, g32p_row07_traceSegment_056_1336_0030, g32p_row07_traceSegment_056_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1397 15 15, g32p_row07_traceSegment_056_1397_0015, g32p_row07_traceSegment_056_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1427 15 16, g32p_row07_traceSegment_056_1427_0015, g32p_row07_traceSegment_056_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1397 30 31, g32p_row07_traceSegment_056_1397_0030, g32p_row07_traceSegment_056_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_056 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1336 61 61, g32p_row07_traceSegment_056_1336_0061, g32p_row07_traceSegment_056_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_056 1215 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1215 121 122, g32p_row07_traceSegment_056_1215_0121, g32p_row07_traceSegment_056_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_056 972 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 972 243 243, g32p_row07_traceSegment_056_0972_0243, g32p_row07_traceSegment_056_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1458 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1458 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1458 15 15, g32p_row07_traceSegment_056_1458_0015, g32p_row07_traceSegment_056_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1488 15 15, g32p_row07_traceSegment_056_1488_0015, g32p_row07_traceSegment_056_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_056 1458 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1458 30 30, g32p_row07_traceSegment_056_1458_0030, g32p_row07_traceSegment_056_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1518 15 15, g32p_row07_traceSegment_056_1518_0015, g32p_row07_traceSegment_056_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1548 15 16, g32p_row07_traceSegment_056_1548_0015, g32p_row07_traceSegment_056_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1518 30 31, g32p_row07_traceSegment_056_1518_0030, g32p_row07_traceSegment_056_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_056 1458 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1458 60 61, g32p_row07_traceSegment_056_1458_0060, g32p_row07_traceSegment_056_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1579 15 15, g32p_row07_traceSegment_056_1579_0015, g32p_row07_traceSegment_056_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1609 15 16, g32p_row07_traceSegment_056_1609_0015, g32p_row07_traceSegment_056_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1579 30 31, g32p_row07_traceSegment_056_1579_0030, g32p_row07_traceSegment_056_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1640 15 15, g32p_row07_traceSegment_056_1640_0015, g32p_row07_traceSegment_056_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1670 15 16, g32p_row07_traceSegment_056_1670_0015, g32p_row07_traceSegment_056_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1640 30 31, g32p_row07_traceSegment_056_1640_0030, g32p_row07_traceSegment_056_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_056 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1579 61 61, g32p_row07_traceSegment_056_1579_0061, g32p_row07_traceSegment_056_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_056 1458 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1458 121 122, g32p_row07_traceSegment_056_1458_0121, g32p_row07_traceSegment_056_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1701 15 15, g32p_row07_traceSegment_056_1701_0015, g32p_row07_traceSegment_056_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1731 15 15, g32p_row07_traceSegment_056_1731_0015, g32p_row07_traceSegment_056_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_056 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1701 30 30, g32p_row07_traceSegment_056_1701_0030, g32p_row07_traceSegment_056_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1761 15 15, g32p_row07_traceSegment_056_1761_0015, g32p_row07_traceSegment_056_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1791 15 16, g32p_row07_traceSegment_056_1791_0015, g32p_row07_traceSegment_056_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1761 30 31, g32p_row07_traceSegment_056_1761_0030, g32p_row07_traceSegment_056_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_056 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1701 60 61, g32p_row07_traceSegment_056_1701_0060, g32p_row07_traceSegment_056_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1822 15 15, g32p_row07_traceSegment_056_1822_0015, g32p_row07_traceSegment_056_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1852 15 16, g32p_row07_traceSegment_056_1852_0015, g32p_row07_traceSegment_056_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1822 30 31, g32p_row07_traceSegment_056_1822_0030, g32p_row07_traceSegment_056_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_056 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1883 15 15, g32p_row07_traceSegment_056_1883_0015, g32p_row07_traceSegment_056_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_056 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_056 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_056_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_056 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1913 15 16, g32p_row07_traceSegment_056_1913_0015, g32p_row07_traceSegment_056_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_056 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1883 30 31, g32p_row07_traceSegment_056_1883_0030, g32p_row07_traceSegment_056_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_056 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1822 61 61, g32p_row07_traceSegment_056_1822_0061, g32p_row07_traceSegment_056_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_056 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1701 121 122, g32p_row07_traceSegment_056_1701_0121, g32p_row07_traceSegment_056_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_056_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_056 1458 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 1458 243 243, g32p_row07_traceSegment_056_1458_0243, g32p_row07_traceSegment_056_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_056 972 972 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 972 486 486, g32p_row07_traceSegment_056_0972_0486, g32p_row07_traceSegment_056_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_056_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_056 0 1944 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_056 0 972 972, g32p_row07_traceSegment_056_0000_0972, g32p_row07_traceSegment_056_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 56 = [0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_056_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_062 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 62 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_062_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 0 15 15, g32p_row07_traceSegment_062_0000_0015, g32p_row07_traceSegment_062_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 30 15 15, g32p_row07_traceSegment_062_0030_0015, g32p_row07_traceSegment_062_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_062 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 0 30 30, g32p_row07_traceSegment_062_0000_0030, g32p_row07_traceSegment_062_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 75 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 60 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 60 15 15, g32p_row07_traceSegment_062_0060_0015, g32p_row07_traceSegment_062_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 90 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 105 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 90 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 90 15 16, g32p_row07_traceSegment_062_0090_0015, g32p_row07_traceSegment_062_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 60 61 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 60 30 31, g32p_row07_traceSegment_062_0060_0030, g32p_row07_traceSegment_062_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_062 0 121 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 0 60 61, g32p_row07_traceSegment_062_0000_0060, g32p_row07_traceSegment_062_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 121 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 136 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 121 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 121 15 15, g32p_row07_traceSegment_062_0121_0015, g32p_row07_traceSegment_062_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 151 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 151 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 151 15 16, g32p_row07_traceSegment_062_0151_0015, g32p_row07_traceSegment_062_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 121 61 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 121 30 31, g32p_row07_traceSegment_062_0121_0030, g32p_row07_traceSegment_062_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 182 15 15, g32p_row07_traceSegment_062_0182_0015, g32p_row07_traceSegment_062_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 212 15 16, g32p_row07_traceSegment_062_0212_0015, g32p_row07_traceSegment_062_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 182 30 31, g32p_row07_traceSegment_062_0182_0030, g32p_row07_traceSegment_062_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_062 121 122 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 121 61 61, g32p_row07_traceSegment_062_0121_0061, g32p_row07_traceSegment_062_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_062 0 243 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 0 121 122, g32p_row07_traceSegment_062_0000_0121, g32p_row07_traceSegment_062_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 243 15 15, g32p_row07_traceSegment_062_0243_0015, g32p_row07_traceSegment_062_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 273 15 15, g32p_row07_traceSegment_062_0273_0015, g32p_row07_traceSegment_062_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_062 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 243 30 30, g32p_row07_traceSegment_062_0243_0030, g32p_row07_traceSegment_062_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 303 15 15, g32p_row07_traceSegment_062_0303_0015, g32p_row07_traceSegment_062_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 333 15 16, g32p_row07_traceSegment_062_0333_0015, g32p_row07_traceSegment_062_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 303 30 31, g32p_row07_traceSegment_062_0303_0030, g32p_row07_traceSegment_062_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_062 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 243 60 61, g32p_row07_traceSegment_062_0243_0060, g32p_row07_traceSegment_062_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 364 15 15, g32p_row07_traceSegment_062_0364_0015, g32p_row07_traceSegment_062_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 394 15 16, g32p_row07_traceSegment_062_0394_0015, g32p_row07_traceSegment_062_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 364 30 31, g32p_row07_traceSegment_062_0364_0030, g32p_row07_traceSegment_062_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 425 15 15, g32p_row07_traceSegment_062_0425_0015, g32p_row07_traceSegment_062_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 455 15 16, g32p_row07_traceSegment_062_0455_0015, g32p_row07_traceSegment_062_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 425 30 31, g32p_row07_traceSegment_062_0425_0030, g32p_row07_traceSegment_062_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_062 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 364 61 61, g32p_row07_traceSegment_062_0364_0061, g32p_row07_traceSegment_062_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_062 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 243 121 122, g32p_row07_traceSegment_062_0243_0121, g32p_row07_traceSegment_062_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_062 0 486 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 0 243 243, g32p_row07_traceSegment_062_0000_0243, g32p_row07_traceSegment_062_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 486 15 15, g32p_row07_traceSegment_062_0486_0015, g32p_row07_traceSegment_062_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 516 15 15, g32p_row07_traceSegment_062_0516_0015, g32p_row07_traceSegment_062_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_062 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 486 30 30, g32p_row07_traceSegment_062_0486_0030, g32p_row07_traceSegment_062_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 546 15 15, g32p_row07_traceSegment_062_0546_0015, g32p_row07_traceSegment_062_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 576 15 16, g32p_row07_traceSegment_062_0576_0015, g32p_row07_traceSegment_062_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 546 30 31, g32p_row07_traceSegment_062_0546_0030, g32p_row07_traceSegment_062_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_062 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 486 60 61, g32p_row07_traceSegment_062_0486_0060, g32p_row07_traceSegment_062_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 607 15 15, g32p_row07_traceSegment_062_0607_0015, g32p_row07_traceSegment_062_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 637 15 16, g32p_row07_traceSegment_062_0637_0015, g32p_row07_traceSegment_062_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 607 30 31, g32p_row07_traceSegment_062_0607_0030, g32p_row07_traceSegment_062_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 668 15 15, g32p_row07_traceSegment_062_0668_0015, g32p_row07_traceSegment_062_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 698 15 16, g32p_row07_traceSegment_062_0698_0015, g32p_row07_traceSegment_062_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 668 30 31, g32p_row07_traceSegment_062_0668_0030, g32p_row07_traceSegment_062_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_062 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 607 61 61, g32p_row07_traceSegment_062_0607_0061, g32p_row07_traceSegment_062_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_062 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 486 121 122, g32p_row07_traceSegment_062_0486_0121, g32p_row07_traceSegment_062_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 729 15 15, g32p_row07_traceSegment_062_0729_0015, g32p_row07_traceSegment_062_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 759 15 15, g32p_row07_traceSegment_062_0759_0015, g32p_row07_traceSegment_062_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_062 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 729 30 30, g32p_row07_traceSegment_062_0729_0030, g32p_row07_traceSegment_062_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 789 15 15, g32p_row07_traceSegment_062_0789_0015, g32p_row07_traceSegment_062_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 819 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 834 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 819 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 819 15 16, g32p_row07_traceSegment_062_0819_0015, g32p_row07_traceSegment_062_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 789 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 789 30 31, g32p_row07_traceSegment_062_0789_0030, g32p_row07_traceSegment_062_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_062 729 121 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 729 60 61, g32p_row07_traceSegment_062_0729_0060, g32p_row07_traceSegment_062_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 865 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 850 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 850 15 15, g32p_row07_traceSegment_062_0850_0015, g32p_row07_traceSegment_062_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 880 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 895 16 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 880 31 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 880 15 16, g32p_row07_traceSegment_062_0880_0015, g32p_row07_traceSegment_062_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 850 61 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 850 30 31, g32p_row07_traceSegment_062_0850_0030, g32p_row07_traceSegment_062_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 911 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 926 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 911 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 911 15 15, g32p_row07_traceSegment_062_0911_0015, g32p_row07_traceSegment_062_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 956 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 941 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 941 15 16, g32p_row07_traceSegment_062_0941_0015, g32p_row07_traceSegment_062_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 911 61 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 911 30 31, g32p_row07_traceSegment_062_0911_0030, g32p_row07_traceSegment_062_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_062 850 122 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 850 61 61, g32p_row07_traceSegment_062_0850_0061, g32p_row07_traceSegment_062_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_062 729 243 = [0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 729 121 122, g32p_row07_traceSegment_062_0729_0121, g32p_row07_traceSegment_062_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_062 486 486 = [0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 486 243 243, g32p_row07_traceSegment_062_0486_0243, g32p_row07_traceSegment_062_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_062 0 972 = [0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 0 486 486, g32p_row07_traceSegment_062_0000_0486, g32p_row07_traceSegment_062_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 972 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 987 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 972 30 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 972 15 15, g32p_row07_traceSegment_062_0972_0015, g32p_row07_traceSegment_062_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1002 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1017 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1002 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1002 15 15, g32p_row07_traceSegment_062_1002_0015, g32p_row07_traceSegment_062_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_062 972 60 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 972 30 30, g32p_row07_traceSegment_062_0972_0030, g32p_row07_traceSegment_062_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1032 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1047 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1032 30 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1032 15 15, g32p_row07_traceSegment_062_1032_0015, g32p_row07_traceSegment_062_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1062 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1062 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1062 15 16, g32p_row07_traceSegment_062_1062_0015, g32p_row07_traceSegment_062_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1032 61 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1032 30 31, g32p_row07_traceSegment_062_1032_0030, g32p_row07_traceSegment_062_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_062 972 121 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 972 60 61, g32p_row07_traceSegment_062_0972_0060, g32p_row07_traceSegment_062_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1093 15 15, g32p_row07_traceSegment_062_1093_0015, g32p_row07_traceSegment_062_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1123 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1138 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1123 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1123 15 16, g32p_row07_traceSegment_062_1123_0015, g32p_row07_traceSegment_062_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1093 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1093 30 31, g32p_row07_traceSegment_062_1093_0030, g32p_row07_traceSegment_062_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1154 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1169 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1154 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1154 15 15, g32p_row07_traceSegment_062_1154_0015, g32p_row07_traceSegment_062_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1184 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1199 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1184 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1184 15 16, g32p_row07_traceSegment_062_1184_0015, g32p_row07_traceSegment_062_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1154 61 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1154 30 31, g32p_row07_traceSegment_062_1154_0030, g32p_row07_traceSegment_062_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_062 1093 122 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1093 61 61, g32p_row07_traceSegment_062_1093_0061, g32p_row07_traceSegment_062_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_062 972 243 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 972 121 122, g32p_row07_traceSegment_062_0972_0121, g32p_row07_traceSegment_062_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1215 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1230 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1215 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1215 15 15, g32p_row07_traceSegment_062_1215_0015, g32p_row07_traceSegment_062_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1260 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1245 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1245 15 15, g32p_row07_traceSegment_062_1245_0015, g32p_row07_traceSegment_062_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_062 1215 60 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1215 30 30, g32p_row07_traceSegment_062_1215_0030, g32p_row07_traceSegment_062_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1275 15 15, g32p_row07_traceSegment_062_1275_0015, g32p_row07_traceSegment_062_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1305 15 16, g32p_row07_traceSegment_062_1305_0015, g32p_row07_traceSegment_062_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1275 30 31, g32p_row07_traceSegment_062_1275_0030, g32p_row07_traceSegment_062_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_062 1215 121 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1215 60 61, g32p_row07_traceSegment_062_1215_0060, g32p_row07_traceSegment_062_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1336 15 15, g32p_row07_traceSegment_062_1336_0015, g32p_row07_traceSegment_062_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1366 15 16, g32p_row07_traceSegment_062_1366_0015, g32p_row07_traceSegment_062_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1336 30 31, g32p_row07_traceSegment_062_1336_0030, g32p_row07_traceSegment_062_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1397 15 15, g32p_row07_traceSegment_062_1397_0015, g32p_row07_traceSegment_062_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1427 15 16, g32p_row07_traceSegment_062_1427_0015, g32p_row07_traceSegment_062_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1397 30 31, g32p_row07_traceSegment_062_1397_0030, g32p_row07_traceSegment_062_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_062 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1336 61 61, g32p_row07_traceSegment_062_1336_0061, g32p_row07_traceSegment_062_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_062 1215 243 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1215 121 122, g32p_row07_traceSegment_062_1215_0121, g32p_row07_traceSegment_062_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_062 972 486 = [0, 0, 39] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 972 243 243, g32p_row07_traceSegment_062_0972_0243, g32p_row07_traceSegment_062_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1458 15 15, g32p_row07_traceSegment_062_1458_0015, g32p_row07_traceSegment_062_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1488 15 15, g32p_row07_traceSegment_062_1488_0015, g32p_row07_traceSegment_062_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_062 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1458 30 30, g32p_row07_traceSegment_062_1458_0030, g32p_row07_traceSegment_062_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1518 15 15, g32p_row07_traceSegment_062_1518_0015, g32p_row07_traceSegment_062_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1548 15 16, g32p_row07_traceSegment_062_1548_0015, g32p_row07_traceSegment_062_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1518 30 31, g32p_row07_traceSegment_062_1518_0030, g32p_row07_traceSegment_062_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_062 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1458 60 61, g32p_row07_traceSegment_062_1458_0060, g32p_row07_traceSegment_062_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1579 15 15, g32p_row07_traceSegment_062_1579_0015, g32p_row07_traceSegment_062_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1609 15 16, g32p_row07_traceSegment_062_1609_0015, g32p_row07_traceSegment_062_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1579 30 31, g32p_row07_traceSegment_062_1579_0030, g32p_row07_traceSegment_062_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1640 15 15, g32p_row07_traceSegment_062_1640_0015, g32p_row07_traceSegment_062_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1670 15 16, g32p_row07_traceSegment_062_1670_0015, g32p_row07_traceSegment_062_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1640 30 31, g32p_row07_traceSegment_062_1640_0030, g32p_row07_traceSegment_062_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_062 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1579 61 61, g32p_row07_traceSegment_062_1579_0061, g32p_row07_traceSegment_062_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_062 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1458 121 122, g32p_row07_traceSegment_062_1458_0121, g32p_row07_traceSegment_062_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1701 15 15, g32p_row07_traceSegment_062_1701_0015, g32p_row07_traceSegment_062_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1731 15 15, g32p_row07_traceSegment_062_1731_0015, g32p_row07_traceSegment_062_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_062 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1701 30 30, g32p_row07_traceSegment_062_1701_0030, g32p_row07_traceSegment_062_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1761 15 15, g32p_row07_traceSegment_062_1761_0015, g32p_row07_traceSegment_062_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1791 15 16, g32p_row07_traceSegment_062_1791_0015, g32p_row07_traceSegment_062_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1761 30 31, g32p_row07_traceSegment_062_1761_0030, g32p_row07_traceSegment_062_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_062 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1701 60 61, g32p_row07_traceSegment_062_1701_0060, g32p_row07_traceSegment_062_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1822 15 15, g32p_row07_traceSegment_062_1822_0015, g32p_row07_traceSegment_062_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1852 15 16, g32p_row07_traceSegment_062_1852_0015, g32p_row07_traceSegment_062_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1822 30 31, g32p_row07_traceSegment_062_1822_0030, g32p_row07_traceSegment_062_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_062 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1883 15 15, g32p_row07_traceSegment_062_1883_0015, g32p_row07_traceSegment_062_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_062 1913 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_062 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_062_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_062 1913 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1913 15 16, g32p_row07_traceSegment_062_1913_0015, g32p_row07_traceSegment_062_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_062 1883 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1883 30 31, g32p_row07_traceSegment_062_1883_0030, g32p_row07_traceSegment_062_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_062 1822 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1822 61 61, g32p_row07_traceSegment_062_1822_0061, g32p_row07_traceSegment_062_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_062 1701 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1701 121 122, g32p_row07_traceSegment_062_1701_0121, g32p_row07_traceSegment_062_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_062_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_062 1458 486 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 1458 243 243, g32p_row07_traceSegment_062_1458_0243, g32p_row07_traceSegment_062_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_062 972 972 = [0, 0, 41] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 972 486 486, g32p_row07_traceSegment_062_0972_0486, g32p_row07_traceSegment_062_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_062_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_062 0 1944 = [0, 0, 72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_062 0 972 972, g32p_row07_traceSegment_062_0000_0972, g32p_row07_traceSegment_062_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_062 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 62 = [0, 0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_062_0000_1944

end HodgeLean.Foundations.Program

end
end
