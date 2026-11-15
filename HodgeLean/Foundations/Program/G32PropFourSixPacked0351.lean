import HodgeLean.Foundations.Program.G32PropFourSixPacked0347
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0350

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_067 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 67 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_067_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 0 15 15, g32p_row07_traceSegment_067_0000_0015, g32p_row07_traceSegment_067_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 30 15 15, g32p_row07_traceSegment_067_0030_0015, g32p_row07_traceSegment_067_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_067 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 0 30 30, g32p_row07_traceSegment_067_0000_0030, g32p_row07_traceSegment_067_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 60 15 15, g32p_row07_traceSegment_067_0060_0015, g32p_row07_traceSegment_067_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 90 15 16, g32p_row07_traceSegment_067_0090_0015, g32p_row07_traceSegment_067_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 60 30 31, g32p_row07_traceSegment_067_0060_0030, g32p_row07_traceSegment_067_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_067 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 0 60 61, g32p_row07_traceSegment_067_0000_0060, g32p_row07_traceSegment_067_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 121 15 15, g32p_row07_traceSegment_067_0121_0015, g32p_row07_traceSegment_067_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 151 15 16, g32p_row07_traceSegment_067_0151_0015, g32p_row07_traceSegment_067_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 121 30 31, g32p_row07_traceSegment_067_0121_0030, g32p_row07_traceSegment_067_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 182 15 15, g32p_row07_traceSegment_067_0182_0015, g32p_row07_traceSegment_067_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 212 15 16, g32p_row07_traceSegment_067_0212_0015, g32p_row07_traceSegment_067_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 182 30 31, g32p_row07_traceSegment_067_0182_0030, g32p_row07_traceSegment_067_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_067 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 121 61 61, g32p_row07_traceSegment_067_0121_0061, g32p_row07_traceSegment_067_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_067 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 0 121 122, g32p_row07_traceSegment_067_0000_0121, g32p_row07_traceSegment_067_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 243 15 15, g32p_row07_traceSegment_067_0243_0015, g32p_row07_traceSegment_067_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 273 15 15, g32p_row07_traceSegment_067_0273_0015, g32p_row07_traceSegment_067_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_067 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 243 30 30, g32p_row07_traceSegment_067_0243_0030, g32p_row07_traceSegment_067_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 303 15 15, g32p_row07_traceSegment_067_0303_0015, g32p_row07_traceSegment_067_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 333 15 16, g32p_row07_traceSegment_067_0333_0015, g32p_row07_traceSegment_067_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 303 30 31, g32p_row07_traceSegment_067_0303_0030, g32p_row07_traceSegment_067_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_067 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 243 60 61, g32p_row07_traceSegment_067_0243_0060, g32p_row07_traceSegment_067_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 379 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 364 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 364 15 15, g32p_row07_traceSegment_067_0364_0015, g32p_row07_traceSegment_067_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 394 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 394 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 394 15 16, g32p_row07_traceSegment_067_0394_0015, g32p_row07_traceSegment_067_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 364 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 364 30 31, g32p_row07_traceSegment_067_0364_0030, g32p_row07_traceSegment_067_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 425 15 15, g32p_row07_traceSegment_067_0425_0015, g32p_row07_traceSegment_067_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 455 15 16, g32p_row07_traceSegment_067_0455_0015, g32p_row07_traceSegment_067_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 425 30 31, g32p_row07_traceSegment_067_0425_0030, g32p_row07_traceSegment_067_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_067 364 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 364 61 61, g32p_row07_traceSegment_067_0364_0061, g32p_row07_traceSegment_067_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_067 243 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 243 121 122, g32p_row07_traceSegment_067_0243_0121, g32p_row07_traceSegment_067_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_067 0 486 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 0 243 243, g32p_row07_traceSegment_067_0000_0243, g32p_row07_traceSegment_067_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 486 15 15, g32p_row07_traceSegment_067_0486_0015, g32p_row07_traceSegment_067_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 516 15 15, g32p_row07_traceSegment_067_0516_0015, g32p_row07_traceSegment_067_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_067 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 486 30 30, g32p_row07_traceSegment_067_0486_0030, g32p_row07_traceSegment_067_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 546 15 15, g32p_row07_traceSegment_067_0546_0015, g32p_row07_traceSegment_067_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 576 15 16, g32p_row07_traceSegment_067_0576_0015, g32p_row07_traceSegment_067_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 546 30 31, g32p_row07_traceSegment_067_0546_0030, g32p_row07_traceSegment_067_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_067 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 486 60 61, g32p_row07_traceSegment_067_0486_0060, g32p_row07_traceSegment_067_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 607 15 15, g32p_row07_traceSegment_067_0607_0015, g32p_row07_traceSegment_067_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 637 15 16, g32p_row07_traceSegment_067_0637_0015, g32p_row07_traceSegment_067_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 607 30 31, g32p_row07_traceSegment_067_0607_0030, g32p_row07_traceSegment_067_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 668 15 15, g32p_row07_traceSegment_067_0668_0015, g32p_row07_traceSegment_067_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 713 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 698 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 698 15 16, g32p_row07_traceSegment_067_0698_0015, g32p_row07_traceSegment_067_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 668 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 668 30 31, g32p_row07_traceSegment_067_0668_0030, g32p_row07_traceSegment_067_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_067 607 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 607 61 61, g32p_row07_traceSegment_067_0607_0061, g32p_row07_traceSegment_067_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_067 486 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 486 121 122, g32p_row07_traceSegment_067_0486_0121, g32p_row07_traceSegment_067_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 729 15 15, g32p_row07_traceSegment_067_0729_0015, g32p_row07_traceSegment_067_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 759 15 15, g32p_row07_traceSegment_067_0759_0015, g32p_row07_traceSegment_067_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_067 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 729 30 30, g32p_row07_traceSegment_067_0729_0030, g32p_row07_traceSegment_067_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 789 15 15, g32p_row07_traceSegment_067_0789_0015, g32p_row07_traceSegment_067_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 819 15 16, g32p_row07_traceSegment_067_0819_0015, g32p_row07_traceSegment_067_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 789 30 31, g32p_row07_traceSegment_067_0789_0030, g32p_row07_traceSegment_067_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_067 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 729 60 61, g32p_row07_traceSegment_067_0729_0060, g32p_row07_traceSegment_067_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 850 15 15, g32p_row07_traceSegment_067_0850_0015, g32p_row07_traceSegment_067_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 880 15 16, g32p_row07_traceSegment_067_0880_0015, g32p_row07_traceSegment_067_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 850 30 31, g32p_row07_traceSegment_067_0850_0030, g32p_row07_traceSegment_067_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 911 15 15, g32p_row07_traceSegment_067_0911_0015, g32p_row07_traceSegment_067_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 941 15 16, g32p_row07_traceSegment_067_0941_0015, g32p_row07_traceSegment_067_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 911 30 31, g32p_row07_traceSegment_067_0911_0030, g32p_row07_traceSegment_067_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_067 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 850 61 61, g32p_row07_traceSegment_067_0850_0061, g32p_row07_traceSegment_067_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_067 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 729 121 122, g32p_row07_traceSegment_067_0729_0121, g32p_row07_traceSegment_067_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_067 486 486 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 486 243 243, g32p_row07_traceSegment_067_0486_0243, g32p_row07_traceSegment_067_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_067 0 972 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 0 486 486, g32p_row07_traceSegment_067_0000_0486, g32p_row07_traceSegment_067_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 972 15 15, g32p_row07_traceSegment_067_0972_0015, g32p_row07_traceSegment_067_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1002 15 15, g32p_row07_traceSegment_067_1002_0015, g32p_row07_traceSegment_067_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_067 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 972 30 30, g32p_row07_traceSegment_067_0972_0030, g32p_row07_traceSegment_067_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1032 15 15, g32p_row07_traceSegment_067_1032_0015, g32p_row07_traceSegment_067_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1062 15 16, g32p_row07_traceSegment_067_1062_0015, g32p_row07_traceSegment_067_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1032 30 31, g32p_row07_traceSegment_067_1032_0030, g32p_row07_traceSegment_067_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_067 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 972 60 61, g32p_row07_traceSegment_067_0972_0060, g32p_row07_traceSegment_067_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1093 15 15, g32p_row07_traceSegment_067_1093_0015, g32p_row07_traceSegment_067_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1123 15 16, g32p_row07_traceSegment_067_1123_0015, g32p_row07_traceSegment_067_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1093 30 31, g32p_row07_traceSegment_067_1093_0030, g32p_row07_traceSegment_067_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1154 15 15, g32p_row07_traceSegment_067_1154_0015, g32p_row07_traceSegment_067_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1184 15 16, g32p_row07_traceSegment_067_1184_0015, g32p_row07_traceSegment_067_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1154 30 31, g32p_row07_traceSegment_067_1154_0030, g32p_row07_traceSegment_067_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_067 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1093 61 61, g32p_row07_traceSegment_067_1093_0061, g32p_row07_traceSegment_067_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_067 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 972 121 122, g32p_row07_traceSegment_067_0972_0121, g32p_row07_traceSegment_067_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1215 15 15, g32p_row07_traceSegment_067_1215_0015, g32p_row07_traceSegment_067_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1245 15 15, g32p_row07_traceSegment_067_1245_0015, g32p_row07_traceSegment_067_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_067 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1215 30 30, g32p_row07_traceSegment_067_1215_0030, g32p_row07_traceSegment_067_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1275 15 15, g32p_row07_traceSegment_067_1275_0015, g32p_row07_traceSegment_067_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1305 15 16, g32p_row07_traceSegment_067_1305_0015, g32p_row07_traceSegment_067_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1275 30 31, g32p_row07_traceSegment_067_1275_0030, g32p_row07_traceSegment_067_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_067 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1215 60 61, g32p_row07_traceSegment_067_1215_0060, g32p_row07_traceSegment_067_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1336 15 15, g32p_row07_traceSegment_067_1336_0015, g32p_row07_traceSegment_067_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1366 15 16, g32p_row07_traceSegment_067_1366_0015, g32p_row07_traceSegment_067_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1336 30 31, g32p_row07_traceSegment_067_1336_0030, g32p_row07_traceSegment_067_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1397 15 15, g32p_row07_traceSegment_067_1397_0015, g32p_row07_traceSegment_067_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1427 15 16, g32p_row07_traceSegment_067_1427_0015, g32p_row07_traceSegment_067_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1397 30 31, g32p_row07_traceSegment_067_1397_0030, g32p_row07_traceSegment_067_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_067 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1336 61 61, g32p_row07_traceSegment_067_1336_0061, g32p_row07_traceSegment_067_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_067 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1215 121 122, g32p_row07_traceSegment_067_1215_0121, g32p_row07_traceSegment_067_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_067 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 972 243 243, g32p_row07_traceSegment_067_0972_0243, g32p_row07_traceSegment_067_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1458 15 15, g32p_row07_traceSegment_067_1458_0015, g32p_row07_traceSegment_067_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1488 15 15, g32p_row07_traceSegment_067_1488_0015, g32p_row07_traceSegment_067_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_067 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1458 30 30, g32p_row07_traceSegment_067_1458_0030, g32p_row07_traceSegment_067_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1518 15 15, g32p_row07_traceSegment_067_1518_0015, g32p_row07_traceSegment_067_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1548 15 16, g32p_row07_traceSegment_067_1548_0015, g32p_row07_traceSegment_067_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1518 30 31, g32p_row07_traceSegment_067_1518_0030, g32p_row07_traceSegment_067_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_067 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1458 60 61, g32p_row07_traceSegment_067_1458_0060, g32p_row07_traceSegment_067_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1579 15 15, g32p_row07_traceSegment_067_1579_0015, g32p_row07_traceSegment_067_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1609 15 16, g32p_row07_traceSegment_067_1609_0015, g32p_row07_traceSegment_067_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1579 30 31, g32p_row07_traceSegment_067_1579_0030, g32p_row07_traceSegment_067_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1640 15 15, g32p_row07_traceSegment_067_1640_0015, g32p_row07_traceSegment_067_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1670 15 16, g32p_row07_traceSegment_067_1670_0015, g32p_row07_traceSegment_067_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1640 30 31, g32p_row07_traceSegment_067_1640_0030, g32p_row07_traceSegment_067_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_067 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1579 61 61, g32p_row07_traceSegment_067_1579_0061, g32p_row07_traceSegment_067_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_067 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1458 121 122, g32p_row07_traceSegment_067_1458_0121, g32p_row07_traceSegment_067_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1701 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1701 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1701 15 15, g32p_row07_traceSegment_067_1701_0015, g32p_row07_traceSegment_067_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1731 15 15, g32p_row07_traceSegment_067_1731_0015, g32p_row07_traceSegment_067_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_067 1701 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1701 30 30, g32p_row07_traceSegment_067_1701_0030, g32p_row07_traceSegment_067_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1761 15 15, g32p_row07_traceSegment_067_1761_0015, g32p_row07_traceSegment_067_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1791 15 16, g32p_row07_traceSegment_067_1791_0015, g32p_row07_traceSegment_067_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1761 30 31, g32p_row07_traceSegment_067_1761_0030, g32p_row07_traceSegment_067_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_067 1701 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1701 60 61, g32p_row07_traceSegment_067_1701_0060, g32p_row07_traceSegment_067_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1822 15 15, g32p_row07_traceSegment_067_1822_0015, g32p_row07_traceSegment_067_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1852 15 16, g32p_row07_traceSegment_067_1852_0015, g32p_row07_traceSegment_067_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1822 30 31, g32p_row07_traceSegment_067_1822_0030, g32p_row07_traceSegment_067_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_067 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1883 15 15, g32p_row07_traceSegment_067_1883_0015, g32p_row07_traceSegment_067_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_067 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_067 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_067_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_067 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1913 15 16, g32p_row07_traceSegment_067_1913_0015, g32p_row07_traceSegment_067_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_067 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1883 30 31, g32p_row07_traceSegment_067_1883_0030, g32p_row07_traceSegment_067_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_067 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1822 61 61, g32p_row07_traceSegment_067_1822_0061, g32p_row07_traceSegment_067_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_067 1701 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1701 121 122, g32p_row07_traceSegment_067_1701_0121, g32p_row07_traceSegment_067_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_067_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_067 1458 486 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 1458 243 243, g32p_row07_traceSegment_067_1458_0243, g32p_row07_traceSegment_067_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_067 972 972 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 972 486 486, g32p_row07_traceSegment_067_0972_0486, g32p_row07_traceSegment_067_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_067_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_067 0 1944 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_067 0 972 972, g32p_row07_traceSegment_067_0000_0972, g32p_row07_traceSegment_067_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 67 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_067_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_068 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 68 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_068_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 15 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 0 15 15, g32p_row07_traceSegment_068_0000_0015, g32p_row07_traceSegment_068_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 30 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 45 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 30 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 30 15 15, g32p_row07_traceSegment_068_0030_0015, g32p_row07_traceSegment_068_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_068 0 60 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 0 30 30, g32p_row07_traceSegment_068_0000_0030, g32p_row07_traceSegment_068_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 60 15 15, g32p_row07_traceSegment_068_0060_0015, g32p_row07_traceSegment_068_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 90 15 16, g32p_row07_traceSegment_068_0090_0015, g32p_row07_traceSegment_068_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 60 30 31, g32p_row07_traceSegment_068_0060_0030, g32p_row07_traceSegment_068_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_068 0 121 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 0 60 61, g32p_row07_traceSegment_068_0000_0060, g32p_row07_traceSegment_068_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 121 15 15, g32p_row07_traceSegment_068_0121_0015, g32p_row07_traceSegment_068_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 151 15 16, g32p_row07_traceSegment_068_0151_0015, g32p_row07_traceSegment_068_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 121 30 31, g32p_row07_traceSegment_068_0121_0030, g32p_row07_traceSegment_068_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 182 15 15, g32p_row07_traceSegment_068_0182_0015, g32p_row07_traceSegment_068_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 212 15 16, g32p_row07_traceSegment_068_0212_0015, g32p_row07_traceSegment_068_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 182 30 31, g32p_row07_traceSegment_068_0182_0030, g32p_row07_traceSegment_068_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_068 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 121 61 61, g32p_row07_traceSegment_068_0121_0061, g32p_row07_traceSegment_068_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_068 0 243 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 0 121 122, g32p_row07_traceSegment_068_0000_0121, g32p_row07_traceSegment_068_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 243 15 15, g32p_row07_traceSegment_068_0243_0015, g32p_row07_traceSegment_068_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 273 15 15, g32p_row07_traceSegment_068_0273_0015, g32p_row07_traceSegment_068_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_068 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 243 30 30, g32p_row07_traceSegment_068_0243_0030, g32p_row07_traceSegment_068_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 303 15 15, g32p_row07_traceSegment_068_0303_0015, g32p_row07_traceSegment_068_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 333 15 16, g32p_row07_traceSegment_068_0333_0015, g32p_row07_traceSegment_068_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 303 30 31, g32p_row07_traceSegment_068_0303_0030, g32p_row07_traceSegment_068_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_068 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 243 60 61, g32p_row07_traceSegment_068_0243_0060, g32p_row07_traceSegment_068_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 364 15 15, g32p_row07_traceSegment_068_0364_0015, g32p_row07_traceSegment_068_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 394 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 409 16 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 394 31 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 394 15 16, g32p_row07_traceSegment_068_0394_0015, g32p_row07_traceSegment_068_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 364 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 364 30 31, g32p_row07_traceSegment_068_0364_0030, g32p_row07_traceSegment_068_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 425 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 440 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 425 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 425 15 15, g32p_row07_traceSegment_068_0425_0015, g32p_row07_traceSegment_068_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 455 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 470 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 455 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 455 15 16, g32p_row07_traceSegment_068_0455_0015, g32p_row07_traceSegment_068_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 425 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 425 30 31, g32p_row07_traceSegment_068_0425_0030, g32p_row07_traceSegment_068_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_068 364 122 = [10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 364 61 61, g32p_row07_traceSegment_068_0364_0061, g32p_row07_traceSegment_068_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_068 243 243 = [10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 243 121 122, g32p_row07_traceSegment_068_0243_0121, g32p_row07_traceSegment_068_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_068 0 486 = [17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 0 243 243, g32p_row07_traceSegment_068_0000_0243, g32p_row07_traceSegment_068_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 486 15 15, g32p_row07_traceSegment_068_0486_0015, g32p_row07_traceSegment_068_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 516 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 531 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 516 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 516 15 15, g32p_row07_traceSegment_068_0516_0015, g32p_row07_traceSegment_068_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_068 486 60 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 486 30 30, g32p_row07_traceSegment_068_0486_0030, g32p_row07_traceSegment_068_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 546 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 561 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 546 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 546 15 15, g32p_row07_traceSegment_068_0546_0015, g32p_row07_traceSegment_068_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 576 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 591 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 576 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 576 15 16, g32p_row07_traceSegment_068_0576_0015, g32p_row07_traceSegment_068_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 546 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 546 30 31, g32p_row07_traceSegment_068_0546_0030, g32p_row07_traceSegment_068_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_068 486 121 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 486 60 61, g32p_row07_traceSegment_068_0486_0060, g32p_row07_traceSegment_068_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 607 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 622 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 607 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 607 15 15, g32p_row07_traceSegment_068_0607_0015, g32p_row07_traceSegment_068_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 637 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 652 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 637 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 637 15 16, g32p_row07_traceSegment_068_0637_0015, g32p_row07_traceSegment_068_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 607 61 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 607 30 31, g32p_row07_traceSegment_068_0607_0030, g32p_row07_traceSegment_068_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 683 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 668 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 668 15 15, g32p_row07_traceSegment_068_0668_0015, g32p_row07_traceSegment_068_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 698 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 713 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 698 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 698 15 16, g32p_row07_traceSegment_068_0698_0015, g32p_row07_traceSegment_068_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 668 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 668 30 31, g32p_row07_traceSegment_068_0668_0030, g32p_row07_traceSegment_068_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_068 607 122 = [14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 607 61 61, g32p_row07_traceSegment_068_0607_0061, g32p_row07_traceSegment_068_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_068 486 243 = [23] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 486 121 122, g32p_row07_traceSegment_068_0486_0121, g32p_row07_traceSegment_068_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 729 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 744 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 729 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 729 15 15, g32p_row07_traceSegment_068_0729_0015, g32p_row07_traceSegment_068_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 759 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 759 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 759 15 15, g32p_row07_traceSegment_068_0759_0015, g32p_row07_traceSegment_068_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_068 729 60 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 729 30 30, g32p_row07_traceSegment_068_0729_0030, g32p_row07_traceSegment_068_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 789 15 15, g32p_row07_traceSegment_068_0789_0015, g32p_row07_traceSegment_068_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 819 15 16, g32p_row07_traceSegment_068_0819_0015, g32p_row07_traceSegment_068_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 789 30 31, g32p_row07_traceSegment_068_0789_0030, g32p_row07_traceSegment_068_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_068 729 121 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 729 60 61, g32p_row07_traceSegment_068_0729_0060, g32p_row07_traceSegment_068_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 850 15 15, g32p_row07_traceSegment_068_0850_0015, g32p_row07_traceSegment_068_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 880 15 16, g32p_row07_traceSegment_068_0880_0015, g32p_row07_traceSegment_068_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 850 30 31, g32p_row07_traceSegment_068_0850_0030, g32p_row07_traceSegment_068_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 911 15 15, g32p_row07_traceSegment_068_0911_0015, g32p_row07_traceSegment_068_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 941 15 16, g32p_row07_traceSegment_068_0941_0015, g32p_row07_traceSegment_068_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 911 30 31, g32p_row07_traceSegment_068_0911_0030, g32p_row07_traceSegment_068_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_068 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 850 61 61, g32p_row07_traceSegment_068_0850_0061, g32p_row07_traceSegment_068_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_068 729 243 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 729 121 122, g32p_row07_traceSegment_068_0729_0121, g32p_row07_traceSegment_068_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_068 486 486 = [27] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 486 243 243, g32p_row07_traceSegment_068_0486_0243, g32p_row07_traceSegment_068_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_068 0 972 = [44] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 0 486 486, g32p_row07_traceSegment_068_0000_0486, g32p_row07_traceSegment_068_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 972 15 15, g32p_row07_traceSegment_068_0972_0015, g32p_row07_traceSegment_068_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1002 15 15, g32p_row07_traceSegment_068_1002_0015, g32p_row07_traceSegment_068_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_068 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 972 30 30, g32p_row07_traceSegment_068_0972_0030, g32p_row07_traceSegment_068_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1032 15 15, g32p_row07_traceSegment_068_1032_0015, g32p_row07_traceSegment_068_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1062 15 16, g32p_row07_traceSegment_068_1062_0015, g32p_row07_traceSegment_068_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1032 30 31, g32p_row07_traceSegment_068_1032_0030, g32p_row07_traceSegment_068_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_068 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 972 60 61, g32p_row07_traceSegment_068_0972_0060, g32p_row07_traceSegment_068_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1093 15 15, g32p_row07_traceSegment_068_1093_0015, g32p_row07_traceSegment_068_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1123 15 16, g32p_row07_traceSegment_068_1123_0015, g32p_row07_traceSegment_068_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1093 30 31, g32p_row07_traceSegment_068_1093_0030, g32p_row07_traceSegment_068_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1154 15 15, g32p_row07_traceSegment_068_1154_0015, g32p_row07_traceSegment_068_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1184 15 16, g32p_row07_traceSegment_068_1184_0015, g32p_row07_traceSegment_068_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1154 30 31, g32p_row07_traceSegment_068_1154_0030, g32p_row07_traceSegment_068_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_068 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1093 61 61, g32p_row07_traceSegment_068_1093_0061, g32p_row07_traceSegment_068_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_068 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 972 121 122, g32p_row07_traceSegment_068_0972_0121, g32p_row07_traceSegment_068_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1215 15 15, g32p_row07_traceSegment_068_1215_0015, g32p_row07_traceSegment_068_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1245 15 15, g32p_row07_traceSegment_068_1245_0015, g32p_row07_traceSegment_068_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_068 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1215 30 30, g32p_row07_traceSegment_068_1215_0030, g32p_row07_traceSegment_068_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1275 15 15, g32p_row07_traceSegment_068_1275_0015, g32p_row07_traceSegment_068_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1305 15 16, g32p_row07_traceSegment_068_1305_0015, g32p_row07_traceSegment_068_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1275 30 31, g32p_row07_traceSegment_068_1275_0030, g32p_row07_traceSegment_068_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_068 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1215 60 61, g32p_row07_traceSegment_068_1215_0060, g32p_row07_traceSegment_068_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1336 15 15, g32p_row07_traceSegment_068_1336_0015, g32p_row07_traceSegment_068_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1366 15 16, g32p_row07_traceSegment_068_1366_0015, g32p_row07_traceSegment_068_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1336 30 31, g32p_row07_traceSegment_068_1336_0030, g32p_row07_traceSegment_068_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1397 15 15, g32p_row07_traceSegment_068_1397_0015, g32p_row07_traceSegment_068_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1427 15 16, g32p_row07_traceSegment_068_1427_0015, g32p_row07_traceSegment_068_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1397 30 31, g32p_row07_traceSegment_068_1397_0030, g32p_row07_traceSegment_068_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_068 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1336 61 61, g32p_row07_traceSegment_068_1336_0061, g32p_row07_traceSegment_068_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_068 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1215 121 122, g32p_row07_traceSegment_068_1215_0121, g32p_row07_traceSegment_068_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_068 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 972 243 243, g32p_row07_traceSegment_068_0972_0243, g32p_row07_traceSegment_068_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1458 15 15, g32p_row07_traceSegment_068_1458_0015, g32p_row07_traceSegment_068_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1488 15 15, g32p_row07_traceSegment_068_1488_0015, g32p_row07_traceSegment_068_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_068 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1458 30 30, g32p_row07_traceSegment_068_1458_0030, g32p_row07_traceSegment_068_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1518 15 15, g32p_row07_traceSegment_068_1518_0015, g32p_row07_traceSegment_068_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1548 15 16, g32p_row07_traceSegment_068_1548_0015, g32p_row07_traceSegment_068_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1518 30 31, g32p_row07_traceSegment_068_1518_0030, g32p_row07_traceSegment_068_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_068 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1458 60 61, g32p_row07_traceSegment_068_1458_0060, g32p_row07_traceSegment_068_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1579 15 15, g32p_row07_traceSegment_068_1579_0015, g32p_row07_traceSegment_068_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1609 15 16, g32p_row07_traceSegment_068_1609_0015, g32p_row07_traceSegment_068_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1579 30 31, g32p_row07_traceSegment_068_1579_0030, g32p_row07_traceSegment_068_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1640 15 15, g32p_row07_traceSegment_068_1640_0015, g32p_row07_traceSegment_068_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1670 15 16, g32p_row07_traceSegment_068_1670_0015, g32p_row07_traceSegment_068_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1640 30 31, g32p_row07_traceSegment_068_1640_0030, g32p_row07_traceSegment_068_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_068 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1579 61 61, g32p_row07_traceSegment_068_1579_0061, g32p_row07_traceSegment_068_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_068 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1458 121 122, g32p_row07_traceSegment_068_1458_0121, g32p_row07_traceSegment_068_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1701 15 15, g32p_row07_traceSegment_068_1701_0015, g32p_row07_traceSegment_068_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1731 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1746 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1731 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1731 15 15, g32p_row07_traceSegment_068_1731_0015, g32p_row07_traceSegment_068_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_068 1701 60 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1701 30 30, g32p_row07_traceSegment_068_1701_0030, g32p_row07_traceSegment_068_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1761 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1776 15 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1761 30 = [9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1761 15 15, g32p_row07_traceSegment_068_1761_0015, g32p_row07_traceSegment_068_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1791 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1806 16 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1791 31 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1791 15 16, g32p_row07_traceSegment_068_1791_0015, g32p_row07_traceSegment_068_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1761 61 = [16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1761 30 31, g32p_row07_traceSegment_068_1761_0030, g32p_row07_traceSegment_068_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_068 1701 121 = [22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1701 60 61, g32p_row07_traceSegment_068_1701_0060, g32p_row07_traceSegment_068_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1822 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1837 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1822 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1822 15 15, g32p_row07_traceSegment_068_1822_0015, g32p_row07_traceSegment_068_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1852 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1852 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1852 15 16, g32p_row07_traceSegment_068_1852_0015, g32p_row07_traceSegment_068_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1822 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1822 30 31, g32p_row07_traceSegment_068_1822_0030, g32p_row07_traceSegment_068_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1883 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_068 1883 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1883 15 15, g32p_row07_traceSegment_068_1883_0015, g32p_row07_traceSegment_068_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_068 1913 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_068 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_068_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_068 1913 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1913 15 16, g32p_row07_traceSegment_068_1913_0015, g32p_row07_traceSegment_068_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_068 1883 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1883 30 31, g32p_row07_traceSegment_068_1883_0030, g32p_row07_traceSegment_068_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_068 1822 122 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1822 61 61, g32p_row07_traceSegment_068_1822_0061, g32p_row07_traceSegment_068_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_068 1701 243 = [28] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1701 121 122, g32p_row07_traceSegment_068_1701_0121, g32p_row07_traceSegment_068_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_068_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_068 1458 486 = [28] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 1458 243 243, g32p_row07_traceSegment_068_1458_0243, g32p_row07_traceSegment_068_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_068 972 972 = [28] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 972 486 486, g32p_row07_traceSegment_068_0972_0486, g32p_row07_traceSegment_068_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_068_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_068 0 1944 = [72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_068 0 972 972, g32p_row07_traceSegment_068_0000_0972, g32p_row07_traceSegment_068_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_068 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 68 = [72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_068_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_069_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 15 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 0 15 15, g32p_row07_traceSegment_069_0000_0015, g32p_row07_traceSegment_069_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 30 15 15, g32p_row07_traceSegment_069_0030_0015, g32p_row07_traceSegment_069_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_069 0 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 0 30 30, g32p_row07_traceSegment_069_0000_0030, g32p_row07_traceSegment_069_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 60 15 15, g32p_row07_traceSegment_069_0060_0015, g32p_row07_traceSegment_069_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 90 15 16, g32p_row07_traceSegment_069_0090_0015, g32p_row07_traceSegment_069_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 60 30 31, g32p_row07_traceSegment_069_0060_0030, g32p_row07_traceSegment_069_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_069 0 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 0 60 61, g32p_row07_traceSegment_069_0000_0060, g32p_row07_traceSegment_069_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 121 15 15, g32p_row07_traceSegment_069_0121_0015, g32p_row07_traceSegment_069_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 151 15 16, g32p_row07_traceSegment_069_0151_0015, g32p_row07_traceSegment_069_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 121 30 31, g32p_row07_traceSegment_069_0121_0030, g32p_row07_traceSegment_069_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 182 15 15, g32p_row07_traceSegment_069_0182_0015, g32p_row07_traceSegment_069_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 212 15 16, g32p_row07_traceSegment_069_0212_0015, g32p_row07_traceSegment_069_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 182 30 31, g32p_row07_traceSegment_069_0182_0030, g32p_row07_traceSegment_069_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_069 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 121 61 61, g32p_row07_traceSegment_069_0121_0061, g32p_row07_traceSegment_069_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_069 0 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 0 121 122, g32p_row07_traceSegment_069_0000_0121, g32p_row07_traceSegment_069_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 243 15 15, g32p_row07_traceSegment_069_0243_0015, g32p_row07_traceSegment_069_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 273 15 15, g32p_row07_traceSegment_069_0273_0015, g32p_row07_traceSegment_069_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_069 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 243 30 30, g32p_row07_traceSegment_069_0243_0030, g32p_row07_traceSegment_069_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 303 15 15, g32p_row07_traceSegment_069_0303_0015, g32p_row07_traceSegment_069_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 333 15 16, g32p_row07_traceSegment_069_0333_0015, g32p_row07_traceSegment_069_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 303 30 31, g32p_row07_traceSegment_069_0303_0030, g32p_row07_traceSegment_069_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_069 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 243 60 61, g32p_row07_traceSegment_069_0243_0060, g32p_row07_traceSegment_069_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 364 15 15, g32p_row07_traceSegment_069_0364_0015, g32p_row07_traceSegment_069_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 394 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 409 16 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 394 31 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 394 15 16, g32p_row07_traceSegment_069_0394_0015, g32p_row07_traceSegment_069_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 364 61 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 364 30 31, g32p_row07_traceSegment_069_0364_0030, g32p_row07_traceSegment_069_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 425 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 425 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 425 15 15, g32p_row07_traceSegment_069_0425_0015, g32p_row07_traceSegment_069_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 455 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 470 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 455 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 455 15 16, g32p_row07_traceSegment_069_0455_0015, g32p_row07_traceSegment_069_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 425 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 425 30 31, g32p_row07_traceSegment_069_0425_0030, g32p_row07_traceSegment_069_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_069 364 122 = [10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 364 61 61, g32p_row07_traceSegment_069_0364_0061, g32p_row07_traceSegment_069_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_069 243 243 = [10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 243 121 122, g32p_row07_traceSegment_069_0243_0121, g32p_row07_traceSegment_069_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_069 0 486 = [11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 0 243 243, g32p_row07_traceSegment_069_0000_0243, g32p_row07_traceSegment_069_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 486 15 15, g32p_row07_traceSegment_069_0486_0015, g32p_row07_traceSegment_069_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 516 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 516 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 516 15 15, g32p_row07_traceSegment_069_0516_0015, g32p_row07_traceSegment_069_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_069 486 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 486 30 30, g32p_row07_traceSegment_069_0486_0030, g32p_row07_traceSegment_069_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 546 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 561 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 546 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 546 15 15, g32p_row07_traceSegment_069_0546_0015, g32p_row07_traceSegment_069_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 576 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 591 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 576 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 576 15 16, g32p_row07_traceSegment_069_0576_0015, g32p_row07_traceSegment_069_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 546 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 546 30 31, g32p_row07_traceSegment_069_0546_0030, g32p_row07_traceSegment_069_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_069 486 121 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 486 60 61, g32p_row07_traceSegment_069_0486_0060, g32p_row07_traceSegment_069_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 607 15 15, g32p_row07_traceSegment_069_0607_0015, g32p_row07_traceSegment_069_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 637 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 637 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 637 15 16, g32p_row07_traceSegment_069_0637_0015, g32p_row07_traceSegment_069_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 607 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 607 30 31, g32p_row07_traceSegment_069_0607_0030, g32p_row07_traceSegment_069_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 668 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 668 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 668 15 15, g32p_row07_traceSegment_069_0668_0015, g32p_row07_traceSegment_069_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 698 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 713 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 698 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 698 15 16, g32p_row07_traceSegment_069_0698_0015, g32p_row07_traceSegment_069_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 668 61 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 668 30 31, g32p_row07_traceSegment_069_0668_0030, g32p_row07_traceSegment_069_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_069 607 122 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 607 61 61, g32p_row07_traceSegment_069_0607_0061, g32p_row07_traceSegment_069_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_069 486 243 = [13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 486 121 122, g32p_row07_traceSegment_069_0486_0121, g32p_row07_traceSegment_069_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 729 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 744 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 729 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 729 15 15, g32p_row07_traceSegment_069_0729_0015, g32p_row07_traceSegment_069_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 759 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 759 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 759 15 15, g32p_row07_traceSegment_069_0759_0015, g32p_row07_traceSegment_069_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_069 729 60 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 729 30 30, g32p_row07_traceSegment_069_0729_0030, g32p_row07_traceSegment_069_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 789 15 15, g32p_row07_traceSegment_069_0789_0015, g32p_row07_traceSegment_069_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 819 15 16, g32p_row07_traceSegment_069_0819_0015, g32p_row07_traceSegment_069_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 789 30 31, g32p_row07_traceSegment_069_0789_0030, g32p_row07_traceSegment_069_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_069 729 121 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 729 60 61, g32p_row07_traceSegment_069_0729_0060, g32p_row07_traceSegment_069_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 850 15 15, g32p_row07_traceSegment_069_0850_0015, g32p_row07_traceSegment_069_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 880 15 16, g32p_row07_traceSegment_069_0880_0015, g32p_row07_traceSegment_069_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 850 30 31, g32p_row07_traceSegment_069_0850_0030, g32p_row07_traceSegment_069_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 911 15 15, g32p_row07_traceSegment_069_0911_0015, g32p_row07_traceSegment_069_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 941 15 16, g32p_row07_traceSegment_069_0941_0015, g32p_row07_traceSegment_069_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 911 30 31, g32p_row07_traceSegment_069_0911_0030, g32p_row07_traceSegment_069_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_069 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 850 61 61, g32p_row07_traceSegment_069_0850_0061, g32p_row07_traceSegment_069_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_069 729 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 729 121 122, g32p_row07_traceSegment_069_0729_0121, g32p_row07_traceSegment_069_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_069 486 486 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 486 243 243, g32p_row07_traceSegment_069_0486_0243, g32p_row07_traceSegment_069_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_069 0 972 = [29] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 0 486 486, g32p_row07_traceSegment_069_0000_0486, g32p_row07_traceSegment_069_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 972 15 15, g32p_row07_traceSegment_069_0972_0015, g32p_row07_traceSegment_069_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1002 15 15, g32p_row07_traceSegment_069_1002_0015, g32p_row07_traceSegment_069_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_069 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 972 30 30, g32p_row07_traceSegment_069_0972_0030, g32p_row07_traceSegment_069_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1032 15 15, g32p_row07_traceSegment_069_1032_0015, g32p_row07_traceSegment_069_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1062 15 16, g32p_row07_traceSegment_069_1062_0015, g32p_row07_traceSegment_069_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1032 30 31, g32p_row07_traceSegment_069_1032_0030, g32p_row07_traceSegment_069_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_069 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 972 60 61, g32p_row07_traceSegment_069_0972_0060, g32p_row07_traceSegment_069_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1093 15 15, g32p_row07_traceSegment_069_1093_0015, g32p_row07_traceSegment_069_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1123 15 16, g32p_row07_traceSegment_069_1123_0015, g32p_row07_traceSegment_069_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1093 30 31, g32p_row07_traceSegment_069_1093_0030, g32p_row07_traceSegment_069_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1154 15 15, g32p_row07_traceSegment_069_1154_0015, g32p_row07_traceSegment_069_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1184 15 16, g32p_row07_traceSegment_069_1184_0015, g32p_row07_traceSegment_069_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1154 30 31, g32p_row07_traceSegment_069_1154_0030, g32p_row07_traceSegment_069_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_069 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1093 61 61, g32p_row07_traceSegment_069_1093_0061, g32p_row07_traceSegment_069_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_069 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 972 121 122, g32p_row07_traceSegment_069_0972_0121, g32p_row07_traceSegment_069_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1215 15 15, g32p_row07_traceSegment_069_1215_0015, g32p_row07_traceSegment_069_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1245 15 15, g32p_row07_traceSegment_069_1245_0015, g32p_row07_traceSegment_069_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_069 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1215 30 30, g32p_row07_traceSegment_069_1215_0030, g32p_row07_traceSegment_069_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1275 15 15, g32p_row07_traceSegment_069_1275_0015, g32p_row07_traceSegment_069_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1305 15 16, g32p_row07_traceSegment_069_1305_0015, g32p_row07_traceSegment_069_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1275 30 31, g32p_row07_traceSegment_069_1275_0030, g32p_row07_traceSegment_069_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_069 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1215 60 61, g32p_row07_traceSegment_069_1215_0060, g32p_row07_traceSegment_069_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1336 15 15, g32p_row07_traceSegment_069_1336_0015, g32p_row07_traceSegment_069_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1366 15 16, g32p_row07_traceSegment_069_1366_0015, g32p_row07_traceSegment_069_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1336 30 31, g32p_row07_traceSegment_069_1336_0030, g32p_row07_traceSegment_069_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1397 15 15, g32p_row07_traceSegment_069_1397_0015, g32p_row07_traceSegment_069_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1427 15 16, g32p_row07_traceSegment_069_1427_0015, g32p_row07_traceSegment_069_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1397 30 31, g32p_row07_traceSegment_069_1397_0030, g32p_row07_traceSegment_069_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_069 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1336 61 61, g32p_row07_traceSegment_069_1336_0061, g32p_row07_traceSegment_069_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_069 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1215 121 122, g32p_row07_traceSegment_069_1215_0121, g32p_row07_traceSegment_069_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_069 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 972 243 243, g32p_row07_traceSegment_069_0972_0243, g32p_row07_traceSegment_069_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1458 15 15, g32p_row07_traceSegment_069_1458_0015, g32p_row07_traceSegment_069_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1488 15 15, g32p_row07_traceSegment_069_1488_0015, g32p_row07_traceSegment_069_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_069 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1458 30 30, g32p_row07_traceSegment_069_1458_0030, g32p_row07_traceSegment_069_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1518 15 15, g32p_row07_traceSegment_069_1518_0015, g32p_row07_traceSegment_069_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1548 15 16, g32p_row07_traceSegment_069_1548_0015, g32p_row07_traceSegment_069_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1518 30 31, g32p_row07_traceSegment_069_1518_0030, g32p_row07_traceSegment_069_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_069 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1458 60 61, g32p_row07_traceSegment_069_1458_0060, g32p_row07_traceSegment_069_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1579 15 15, g32p_row07_traceSegment_069_1579_0015, g32p_row07_traceSegment_069_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1609 15 16, g32p_row07_traceSegment_069_1609_0015, g32p_row07_traceSegment_069_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1579 30 31, g32p_row07_traceSegment_069_1579_0030, g32p_row07_traceSegment_069_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1640 15 15, g32p_row07_traceSegment_069_1640_0015, g32p_row07_traceSegment_069_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1670 15 16, g32p_row07_traceSegment_069_1670_0015, g32p_row07_traceSegment_069_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1640 30 31, g32p_row07_traceSegment_069_1640_0030, g32p_row07_traceSegment_069_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_069 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1579 61 61, g32p_row07_traceSegment_069_1579_0061, g32p_row07_traceSegment_069_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_069 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1458 121 122, g32p_row07_traceSegment_069_1458_0121, g32p_row07_traceSegment_069_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1701 15 15, g32p_row07_traceSegment_069_1701_0015, g32p_row07_traceSegment_069_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1731 15 15, g32p_row07_traceSegment_069_1731_0015, g32p_row07_traceSegment_069_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_069 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1701 30 30, g32p_row07_traceSegment_069_1701_0030, g32p_row07_traceSegment_069_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1761 15 15, g32p_row07_traceSegment_069_1761_0015, g32p_row07_traceSegment_069_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1791 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1806 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1791 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1791 15 16, g32p_row07_traceSegment_069_1791_0015, g32p_row07_traceSegment_069_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1761 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1761 30 31, g32p_row07_traceSegment_069_1761_0030, g32p_row07_traceSegment_069_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_069 1701 121 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1701 60 61, g32p_row07_traceSegment_069_1701_0060, g32p_row07_traceSegment_069_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1822 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1837 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1822 30 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1822 15 15, g32p_row07_traceSegment_069_1822_0015, g32p_row07_traceSegment_069_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1852 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1867 16 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1852 31 = [10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1852 15 16, g32p_row07_traceSegment_069_1852_0015, g32p_row07_traceSegment_069_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1822 61 = [16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1822 30 31, g32p_row07_traceSegment_069_1822_0030, g32p_row07_traceSegment_069_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1883 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1898 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_069 1883 30 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1883 15 15, g32p_row07_traceSegment_069_1883_0015, g32p_row07_traceSegment_069_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_069 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_069 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_069_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_069 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1913 15 16, g32p_row07_traceSegment_069_1913_0015, g32p_row07_traceSegment_069_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_069 1883 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1883 30 31, g32p_row07_traceSegment_069_1883_0030, g32p_row07_traceSegment_069_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_069 1822 122 = [21] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1822 61 61, g32p_row07_traceSegment_069_1822_0061, g32p_row07_traceSegment_069_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_069 1701 243 = [25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1701 121 122, g32p_row07_traceSegment_069_1701_0121, g32p_row07_traceSegment_069_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_069_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_069 1458 486 = [25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 1458 243 243, g32p_row07_traceSegment_069_1458_0243, g32p_row07_traceSegment_069_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_069 972 972 = [25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 972 486 486, g32p_row07_traceSegment_069_0972_0486, g32p_row07_traceSegment_069_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_069_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_069 0 1944 = [54] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_069 0 972 972, g32p_row07_traceSegment_069_0000_0972, g32p_row07_traceSegment_069_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 69 = [54] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_069_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row07_tracePolynomial_046 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 46) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 46) (g32p_literalTraceValue 6 46)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_046]
  decide +kernel

theorem g32p_row07_tracePolynomial_053 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 53) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 53) (g32p_literalTraceValue 6 53)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_053]
  decide +kernel

theorem g32p_row07_tracePolynomial_054 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 54) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 54) (g32p_literalTraceValue 6 54)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_054]
  decide +kernel

theorem g32p_row07_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 56) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 56) (g32p_literalTraceValue 6 56)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_056]
  decide +kernel

theorem g32p_row07_tracePolynomial_062 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 62) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 62) (g32p_literalTraceValue 6 62)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row07_traceCoefficients_062]
  decide +kernel

theorem g32p_row07_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 67) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 67) (g32p_literalTraceValue 6 67)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_067]
  decide +kernel

theorem g32p_row07_tracePolynomial_068 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 68) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 68) (g32p_literalTraceValue 6 68)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_068]
  decide +kernel

theorem g32p_row07_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 69) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 69) (g32p_literalTraceValue 6 69)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_069]
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

private def g32p_row07_traceSegment_070 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 70 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_070_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 0 15 15, g32p_row07_traceSegment_070_0000_0015, g32p_row07_traceSegment_070_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 30 15 15, g32p_row07_traceSegment_070_0030_0015, g32p_row07_traceSegment_070_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_070 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 0 30 30, g32p_row07_traceSegment_070_0000_0030, g32p_row07_traceSegment_070_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 60 15 15, g32p_row07_traceSegment_070_0060_0015, g32p_row07_traceSegment_070_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 90 15 16, g32p_row07_traceSegment_070_0090_0015, g32p_row07_traceSegment_070_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 60 30 31, g32p_row07_traceSegment_070_0060_0030, g32p_row07_traceSegment_070_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_070 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 0 60 61, g32p_row07_traceSegment_070_0000_0060, g32p_row07_traceSegment_070_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 121 15 15, g32p_row07_traceSegment_070_0121_0015, g32p_row07_traceSegment_070_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 151 15 16, g32p_row07_traceSegment_070_0151_0015, g32p_row07_traceSegment_070_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 121 30 31, g32p_row07_traceSegment_070_0121_0030, g32p_row07_traceSegment_070_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 182 15 15, g32p_row07_traceSegment_070_0182_0015, g32p_row07_traceSegment_070_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 212 15 16, g32p_row07_traceSegment_070_0212_0015, g32p_row07_traceSegment_070_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 182 30 31, g32p_row07_traceSegment_070_0182_0030, g32p_row07_traceSegment_070_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_070 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 121 61 61, g32p_row07_traceSegment_070_0121_0061, g32p_row07_traceSegment_070_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_070 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 0 121 122, g32p_row07_traceSegment_070_0000_0121, g32p_row07_traceSegment_070_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 243 15 15, g32p_row07_traceSegment_070_0243_0015, g32p_row07_traceSegment_070_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 273 15 15, g32p_row07_traceSegment_070_0273_0015, g32p_row07_traceSegment_070_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_070 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 243 30 30, g32p_row07_traceSegment_070_0243_0030, g32p_row07_traceSegment_070_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 303 15 15, g32p_row07_traceSegment_070_0303_0015, g32p_row07_traceSegment_070_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 333 15 16, g32p_row07_traceSegment_070_0333_0015, g32p_row07_traceSegment_070_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 303 30 31, g32p_row07_traceSegment_070_0303_0030, g32p_row07_traceSegment_070_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_070 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 243 60 61, g32p_row07_traceSegment_070_0243_0060, g32p_row07_traceSegment_070_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 364 15 15, g32p_row07_traceSegment_070_0364_0015, g32p_row07_traceSegment_070_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 394 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 409 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 394 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 394 15 16, g32p_row07_traceSegment_070_0394_0015, g32p_row07_traceSegment_070_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 364 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 364 30 31, g32p_row07_traceSegment_070_0364_0030, g32p_row07_traceSegment_070_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 425 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 440 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 425 30 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 425 15 15, g32p_row07_traceSegment_070_0425_0015, g32p_row07_traceSegment_070_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 455 15 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 470 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 455 31 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 455 15 16, g32p_row07_traceSegment_070_0455_0015, g32p_row07_traceSegment_070_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 425 61 = [15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 425 30 31, g32p_row07_traceSegment_070_0425_0030, g32p_row07_traceSegment_070_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_070 364 122 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 364 61 61, g32p_row07_traceSegment_070_0364_0061, g32p_row07_traceSegment_070_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_070 243 243 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 243 121 122, g32p_row07_traceSegment_070_0243_0121, g32p_row07_traceSegment_070_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_070 0 486 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 0 243 243, g32p_row07_traceSegment_070_0000_0243, g32p_row07_traceSegment_070_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 486 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 501 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 486 30 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 486 15 15, g32p_row07_traceSegment_070_0486_0015, g32p_row07_traceSegment_070_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 516 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 531 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 516 30 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 516 15 15, g32p_row07_traceSegment_070_0516_0015, g32p_row07_traceSegment_070_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_070 486 60 = [13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 486 30 30, g32p_row07_traceSegment_070_0486_0030, g32p_row07_traceSegment_070_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 546 15 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 561 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 546 30 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 546 15 15, g32p_row07_traceSegment_070_0546_0015, g32p_row07_traceSegment_070_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 576 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 591 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 576 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 576 15 16, g32p_row07_traceSegment_070_0576_0015, g32p_row07_traceSegment_070_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 546 61 = [11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 546 30 31, g32p_row07_traceSegment_070_0546_0030, g32p_row07_traceSegment_070_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_070 486 121 = [24] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 486 60 61, g32p_row07_traceSegment_070_0486_0060, g32p_row07_traceSegment_070_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 607 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 622 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 607 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 607 15 15, g32p_row07_traceSegment_070_0607_0015, g32p_row07_traceSegment_070_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 637 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 652 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 637 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 637 15 16, g32p_row07_traceSegment_070_0637_0015, g32p_row07_traceSegment_070_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 607 61 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 607 30 31, g32p_row07_traceSegment_070_0607_0030, g32p_row07_traceSegment_070_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 668 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 683 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 668 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 668 15 15, g32p_row07_traceSegment_070_0668_0015, g32p_row07_traceSegment_070_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 698 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 698 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 698 15 16, g32p_row07_traceSegment_070_0698_0015, g32p_row07_traceSegment_070_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 668 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 668 30 31, g32p_row07_traceSegment_070_0668_0030, g32p_row07_traceSegment_070_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_070 607 122 = [12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 607 61 61, g32p_row07_traceSegment_070_0607_0061, g32p_row07_traceSegment_070_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_070 486 243 = [36] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 486 121 122, g32p_row07_traceSegment_070_0486_0121, g32p_row07_traceSegment_070_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 744 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 729 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 729 15 15, g32p_row07_traceSegment_070_0729_0015, g32p_row07_traceSegment_070_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 759 15 15, g32p_row07_traceSegment_070_0759_0015, g32p_row07_traceSegment_070_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_070 729 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 729 30 30, g32p_row07_traceSegment_070_0729_0030, g32p_row07_traceSegment_070_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 789 15 15, g32p_row07_traceSegment_070_0789_0015, g32p_row07_traceSegment_070_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 819 15 16, g32p_row07_traceSegment_070_0819_0015, g32p_row07_traceSegment_070_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 789 30 31, g32p_row07_traceSegment_070_0789_0030, g32p_row07_traceSegment_070_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_070 729 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 729 60 61, g32p_row07_traceSegment_070_0729_0060, g32p_row07_traceSegment_070_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 850 15 15, g32p_row07_traceSegment_070_0850_0015, g32p_row07_traceSegment_070_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 880 15 16, g32p_row07_traceSegment_070_0880_0015, g32p_row07_traceSegment_070_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 850 30 31, g32p_row07_traceSegment_070_0850_0030, g32p_row07_traceSegment_070_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 911 15 15, g32p_row07_traceSegment_070_0911_0015, g32p_row07_traceSegment_070_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 941 15 16, g32p_row07_traceSegment_070_0941_0015, g32p_row07_traceSegment_070_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 911 30 31, g32p_row07_traceSegment_070_0911_0030, g32p_row07_traceSegment_070_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_070 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 850 61 61, g32p_row07_traceSegment_070_0850_0061, g32p_row07_traceSegment_070_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_070 729 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 729 121 122, g32p_row07_traceSegment_070_0729_0121, g32p_row07_traceSegment_070_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_070 486 486 = [37] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 486 243 243, g32p_row07_traceSegment_070_0486_0243, g32p_row07_traceSegment_070_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_070 0 972 = [55] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 0 486 486, g32p_row07_traceSegment_070_0000_0486, g32p_row07_traceSegment_070_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 972 15 15, g32p_row07_traceSegment_070_0972_0015, g32p_row07_traceSegment_070_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1002 15 15, g32p_row07_traceSegment_070_1002_0015, g32p_row07_traceSegment_070_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_070 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 972 30 30, g32p_row07_traceSegment_070_0972_0030, g32p_row07_traceSegment_070_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1032 15 15, g32p_row07_traceSegment_070_1032_0015, g32p_row07_traceSegment_070_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1062 15 16, g32p_row07_traceSegment_070_1062_0015, g32p_row07_traceSegment_070_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1032 30 31, g32p_row07_traceSegment_070_1032_0030, g32p_row07_traceSegment_070_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_070 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 972 60 61, g32p_row07_traceSegment_070_0972_0060, g32p_row07_traceSegment_070_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1093 15 15, g32p_row07_traceSegment_070_1093_0015, g32p_row07_traceSegment_070_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1123 15 16, g32p_row07_traceSegment_070_1123_0015, g32p_row07_traceSegment_070_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1093 30 31, g32p_row07_traceSegment_070_1093_0030, g32p_row07_traceSegment_070_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1154 15 15, g32p_row07_traceSegment_070_1154_0015, g32p_row07_traceSegment_070_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1184 15 16, g32p_row07_traceSegment_070_1184_0015, g32p_row07_traceSegment_070_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1154 30 31, g32p_row07_traceSegment_070_1154_0030, g32p_row07_traceSegment_070_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_070 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1093 61 61, g32p_row07_traceSegment_070_1093_0061, g32p_row07_traceSegment_070_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_070 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 972 121 122, g32p_row07_traceSegment_070_0972_0121, g32p_row07_traceSegment_070_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1215 15 15, g32p_row07_traceSegment_070_1215_0015, g32p_row07_traceSegment_070_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1245 15 15, g32p_row07_traceSegment_070_1245_0015, g32p_row07_traceSegment_070_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_070 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1215 30 30, g32p_row07_traceSegment_070_1215_0030, g32p_row07_traceSegment_070_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1275 15 15, g32p_row07_traceSegment_070_1275_0015, g32p_row07_traceSegment_070_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1305 15 16, g32p_row07_traceSegment_070_1305_0015, g32p_row07_traceSegment_070_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1275 30 31, g32p_row07_traceSegment_070_1275_0030, g32p_row07_traceSegment_070_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_070 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1215 60 61, g32p_row07_traceSegment_070_1215_0060, g32p_row07_traceSegment_070_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1336 15 15, g32p_row07_traceSegment_070_1336_0015, g32p_row07_traceSegment_070_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1366 15 16, g32p_row07_traceSegment_070_1366_0015, g32p_row07_traceSegment_070_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1336 30 31, g32p_row07_traceSegment_070_1336_0030, g32p_row07_traceSegment_070_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1397 15 15, g32p_row07_traceSegment_070_1397_0015, g32p_row07_traceSegment_070_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1427 15 16, g32p_row07_traceSegment_070_1427_0015, g32p_row07_traceSegment_070_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1397 30 31, g32p_row07_traceSegment_070_1397_0030, g32p_row07_traceSegment_070_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_070 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1336 61 61, g32p_row07_traceSegment_070_1336_0061, g32p_row07_traceSegment_070_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_070 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1215 121 122, g32p_row07_traceSegment_070_1215_0121, g32p_row07_traceSegment_070_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_070 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 972 243 243, g32p_row07_traceSegment_070_0972_0243, g32p_row07_traceSegment_070_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1458 15 15, g32p_row07_traceSegment_070_1458_0015, g32p_row07_traceSegment_070_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1488 15 15, g32p_row07_traceSegment_070_1488_0015, g32p_row07_traceSegment_070_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_070 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1458 30 30, g32p_row07_traceSegment_070_1458_0030, g32p_row07_traceSegment_070_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1518 15 15, g32p_row07_traceSegment_070_1518_0015, g32p_row07_traceSegment_070_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1548 15 16, g32p_row07_traceSegment_070_1548_0015, g32p_row07_traceSegment_070_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1518 30 31, g32p_row07_traceSegment_070_1518_0030, g32p_row07_traceSegment_070_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_070 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1458 60 61, g32p_row07_traceSegment_070_1458_0060, g32p_row07_traceSegment_070_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1579 15 15, g32p_row07_traceSegment_070_1579_0015, g32p_row07_traceSegment_070_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1609 15 16, g32p_row07_traceSegment_070_1609_0015, g32p_row07_traceSegment_070_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1579 30 31, g32p_row07_traceSegment_070_1579_0030, g32p_row07_traceSegment_070_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1640 15 15, g32p_row07_traceSegment_070_1640_0015, g32p_row07_traceSegment_070_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1670 15 16, g32p_row07_traceSegment_070_1670_0015, g32p_row07_traceSegment_070_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1640 30 31, g32p_row07_traceSegment_070_1640_0030, g32p_row07_traceSegment_070_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_070 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1579 61 61, g32p_row07_traceSegment_070_1579_0061, g32p_row07_traceSegment_070_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_070 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1458 121 122, g32p_row07_traceSegment_070_1458_0121, g32p_row07_traceSegment_070_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1701 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1716 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1701 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1701 15 15, g32p_row07_traceSegment_070_1701_0015, g32p_row07_traceSegment_070_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1731 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1746 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1731 30 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1731 15 15, g32p_row07_traceSegment_070_1731_0015, g32p_row07_traceSegment_070_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_070 1701 60 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1701 30 30, g32p_row07_traceSegment_070_1701_0030, g32p_row07_traceSegment_070_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1761 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1761 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1761 15 15, g32p_row07_traceSegment_070_1761_0015, g32p_row07_traceSegment_070_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1791 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1791 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1791 15 16, g32p_row07_traceSegment_070_1791_0015, g32p_row07_traceSegment_070_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1761 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1761 30 31, g32p_row07_traceSegment_070_1761_0030, g32p_row07_traceSegment_070_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_070 1701 121 = [11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1701 60 61, g32p_row07_traceSegment_070_1701_0060, g32p_row07_traceSegment_070_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1822 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1837 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1822 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1822 15 15, g32p_row07_traceSegment_070_1822_0015, g32p_row07_traceSegment_070_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1852 15 16, g32p_row07_traceSegment_070_1852_0015, g32p_row07_traceSegment_070_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1822 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1822 30 31, g32p_row07_traceSegment_070_1822_0030, g32p_row07_traceSegment_070_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1883 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1898 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_070 1883 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1883 15 15, g32p_row07_traceSegment_070_1883_0015, g32p_row07_traceSegment_070_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_070 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_070 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_070_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_070 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1913 15 16, g32p_row07_traceSegment_070_1913_0015, g32p_row07_traceSegment_070_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_070 1883 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1883 30 31, g32p_row07_traceSegment_070_1883_0030, g32p_row07_traceSegment_070_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_070 1822 122 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1822 61 61, g32p_row07_traceSegment_070_1822_0061, g32p_row07_traceSegment_070_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_070 1701 243 = [17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1701 121 122, g32p_row07_traceSegment_070_1701_0121, g32p_row07_traceSegment_070_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_070_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_070 1458 486 = [17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 1458 243 243, g32p_row07_traceSegment_070_1458_0243, g32p_row07_traceSegment_070_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_070 972 972 = [17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 972 486 486, g32p_row07_traceSegment_070_0972_0486, g32p_row07_traceSegment_070_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_070_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_070 0 1944 = [72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_070 0 972 972, g32p_row07_traceSegment_070_0000_0972, g32p_row07_traceSegment_070_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_070 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 70 = [72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_070_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_075 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 75 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_075_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 15 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 0 15 15, g32p_row07_traceSegment_075_0000_0015, g32p_row07_traceSegment_075_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 30 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 45 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 30 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 30 15 15, g32p_row07_traceSegment_075_0030_0015, g32p_row07_traceSegment_075_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_075 0 60 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 0 30 30, g32p_row07_traceSegment_075_0000_0030, g32p_row07_traceSegment_075_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 60 15 15, g32p_row07_traceSegment_075_0060_0015, g32p_row07_traceSegment_075_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 90 15 16, g32p_row07_traceSegment_075_0090_0015, g32p_row07_traceSegment_075_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 60 30 31, g32p_row07_traceSegment_075_0060_0030, g32p_row07_traceSegment_075_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_075 0 121 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 0 60 61, g32p_row07_traceSegment_075_0000_0060, g32p_row07_traceSegment_075_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 121 15 15, g32p_row07_traceSegment_075_0121_0015, g32p_row07_traceSegment_075_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 151 15 16, g32p_row07_traceSegment_075_0151_0015, g32p_row07_traceSegment_075_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 121 30 31, g32p_row07_traceSegment_075_0121_0030, g32p_row07_traceSegment_075_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 182 15 15, g32p_row07_traceSegment_075_0182_0015, g32p_row07_traceSegment_075_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 212 15 16, g32p_row07_traceSegment_075_0212_0015, g32p_row07_traceSegment_075_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 182 30 31, g32p_row07_traceSegment_075_0182_0030, g32p_row07_traceSegment_075_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_075 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 121 61 61, g32p_row07_traceSegment_075_0121_0061, g32p_row07_traceSegment_075_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_075 0 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 0 121 122, g32p_row07_traceSegment_075_0000_0121, g32p_row07_traceSegment_075_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 243 15 15, g32p_row07_traceSegment_075_0243_0015, g32p_row07_traceSegment_075_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 273 15 15, g32p_row07_traceSegment_075_0273_0015, g32p_row07_traceSegment_075_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_075 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 243 30 30, g32p_row07_traceSegment_075_0243_0030, g32p_row07_traceSegment_075_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 303 15 15, g32p_row07_traceSegment_075_0303_0015, g32p_row07_traceSegment_075_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 333 15 16, g32p_row07_traceSegment_075_0333_0015, g32p_row07_traceSegment_075_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 303 30 31, g32p_row07_traceSegment_075_0303_0030, g32p_row07_traceSegment_075_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_075 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 243 60 61, g32p_row07_traceSegment_075_0243_0060, g32p_row07_traceSegment_075_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 364 15 15, g32p_row07_traceSegment_075_0364_0015, g32p_row07_traceSegment_075_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 394 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 409 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 394 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 394 15 16, g32p_row07_traceSegment_075_0394_0015, g32p_row07_traceSegment_075_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 364 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 364 30 31, g32p_row07_traceSegment_075_0364_0030, g32p_row07_traceSegment_075_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 425 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 440 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 425 30 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 425 15 15, g32p_row07_traceSegment_075_0425_0015, g32p_row07_traceSegment_075_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 455 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 470 16 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 455 31 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 455 15 16, g32p_row07_traceSegment_075_0455_0015, g32p_row07_traceSegment_075_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 425 61 = [15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 425 30 31, g32p_row07_traceSegment_075_0425_0030, g32p_row07_traceSegment_075_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_075 364 122 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 364 61 61, g32p_row07_traceSegment_075_0364_0061, g32p_row07_traceSegment_075_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_075 243 243 = [18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 243 121 122, g32p_row07_traceSegment_075_0243_0121, g32p_row07_traceSegment_075_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_075 0 486 = [23] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 0 243 243, g32p_row07_traceSegment_075_0000_0243, g32p_row07_traceSegment_075_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 486 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 501 15 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 486 30 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 486 15 15, g32p_row07_traceSegment_075_0486_0015, g32p_row07_traceSegment_075_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 516 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 531 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 516 30 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 516 15 15, g32p_row07_traceSegment_075_0516_0015, g32p_row07_traceSegment_075_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_075 486 60 = [12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 486 30 30, g32p_row07_traceSegment_075_0486_0030, g32p_row07_traceSegment_075_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 546 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 561 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 546 30 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 546 15 15, g32p_row07_traceSegment_075_0546_0015, g32p_row07_traceSegment_075_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 576 15 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 591 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 576 31 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 576 15 16, g32p_row07_traceSegment_075_0576_0015, g32p_row07_traceSegment_075_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 546 61 = [10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 546 30 31, g32p_row07_traceSegment_075_0546_0030, g32p_row07_traceSegment_075_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_075 486 121 = [22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 486 60 61, g32p_row07_traceSegment_075_0486_0060, g32p_row07_traceSegment_075_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 622 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 607 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 607 15 15, g32p_row07_traceSegment_075_0607_0015, g32p_row07_traceSegment_075_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 637 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 652 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 637 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 637 15 16, g32p_row07_traceSegment_075_0637_0015, g32p_row07_traceSegment_075_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 607 61 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 607 30 31, g32p_row07_traceSegment_075_0607_0030, g32p_row07_traceSegment_075_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 668 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 683 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 668 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 668 15 15, g32p_row07_traceSegment_075_0668_0015, g32p_row07_traceSegment_075_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 698 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 713 16 = [4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 698 31 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 698 15 16, g32p_row07_traceSegment_075_0698_0015, g32p_row07_traceSegment_075_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 668 61 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 668 30 31, g32p_row07_traceSegment_075_0668_0030, g32p_row07_traceSegment_075_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_075 607 122 = [14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 607 61 61, g32p_row07_traceSegment_075_0607_0061, g32p_row07_traceSegment_075_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_075 486 243 = [36] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 486 121 122, g32p_row07_traceSegment_075_0486_0121, g32p_row07_traceSegment_075_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 744 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 729 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 729 15 15, g32p_row07_traceSegment_075_0729_0015, g32p_row07_traceSegment_075_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 759 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 759 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 759 15 15, g32p_row07_traceSegment_075_0759_0015, g32p_row07_traceSegment_075_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_075 729 60 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 729 30 30, g32p_row07_traceSegment_075_0729_0030, g32p_row07_traceSegment_075_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 789 15 15, g32p_row07_traceSegment_075_0789_0015, g32p_row07_traceSegment_075_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 819 15 16, g32p_row07_traceSegment_075_0819_0015, g32p_row07_traceSegment_075_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 789 30 31, g32p_row07_traceSegment_075_0789_0030, g32p_row07_traceSegment_075_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_075 729 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 729 60 61, g32p_row07_traceSegment_075_0729_0060, g32p_row07_traceSegment_075_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 850 15 15, g32p_row07_traceSegment_075_0850_0015, g32p_row07_traceSegment_075_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 880 15 16, g32p_row07_traceSegment_075_0880_0015, g32p_row07_traceSegment_075_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 850 30 31, g32p_row07_traceSegment_075_0850_0030, g32p_row07_traceSegment_075_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 911 15 15, g32p_row07_traceSegment_075_0911_0015, g32p_row07_traceSegment_075_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 941 15 16, g32p_row07_traceSegment_075_0941_0015, g32p_row07_traceSegment_075_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 911 30 31, g32p_row07_traceSegment_075_0911_0030, g32p_row07_traceSegment_075_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_075 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 850 61 61, g32p_row07_traceSegment_075_0850_0061, g32p_row07_traceSegment_075_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_075 729 243 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 729 121 122, g32p_row07_traceSegment_075_0729_0121, g32p_row07_traceSegment_075_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_075 486 486 = [39] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 486 243 243, g32p_row07_traceSegment_075_0486_0243, g32p_row07_traceSegment_075_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_075 0 972 = [62] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 0 486 486, g32p_row07_traceSegment_075_0000_0486, g32p_row07_traceSegment_075_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 972 15 15, g32p_row07_traceSegment_075_0972_0015, g32p_row07_traceSegment_075_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1002 15 15, g32p_row07_traceSegment_075_1002_0015, g32p_row07_traceSegment_075_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_075 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 972 30 30, g32p_row07_traceSegment_075_0972_0030, g32p_row07_traceSegment_075_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1032 15 15, g32p_row07_traceSegment_075_1032_0015, g32p_row07_traceSegment_075_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1062 15 16, g32p_row07_traceSegment_075_1062_0015, g32p_row07_traceSegment_075_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1032 30 31, g32p_row07_traceSegment_075_1032_0030, g32p_row07_traceSegment_075_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_075 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 972 60 61, g32p_row07_traceSegment_075_0972_0060, g32p_row07_traceSegment_075_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1093 15 15, g32p_row07_traceSegment_075_1093_0015, g32p_row07_traceSegment_075_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1123 15 16, g32p_row07_traceSegment_075_1123_0015, g32p_row07_traceSegment_075_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1093 30 31, g32p_row07_traceSegment_075_1093_0030, g32p_row07_traceSegment_075_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1154 15 15, g32p_row07_traceSegment_075_1154_0015, g32p_row07_traceSegment_075_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1184 15 16, g32p_row07_traceSegment_075_1184_0015, g32p_row07_traceSegment_075_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1154 30 31, g32p_row07_traceSegment_075_1154_0030, g32p_row07_traceSegment_075_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_075 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1093 61 61, g32p_row07_traceSegment_075_1093_0061, g32p_row07_traceSegment_075_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_075 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 972 121 122, g32p_row07_traceSegment_075_0972_0121, g32p_row07_traceSegment_075_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1215 15 15, g32p_row07_traceSegment_075_1215_0015, g32p_row07_traceSegment_075_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1245 15 15, g32p_row07_traceSegment_075_1245_0015, g32p_row07_traceSegment_075_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_075 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1215 30 30, g32p_row07_traceSegment_075_1215_0030, g32p_row07_traceSegment_075_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1275 15 15, g32p_row07_traceSegment_075_1275_0015, g32p_row07_traceSegment_075_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1305 15 16, g32p_row07_traceSegment_075_1305_0015, g32p_row07_traceSegment_075_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1275 30 31, g32p_row07_traceSegment_075_1275_0030, g32p_row07_traceSegment_075_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_075 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1215 60 61, g32p_row07_traceSegment_075_1215_0060, g32p_row07_traceSegment_075_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1336 15 15, g32p_row07_traceSegment_075_1336_0015, g32p_row07_traceSegment_075_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1366 15 16, g32p_row07_traceSegment_075_1366_0015, g32p_row07_traceSegment_075_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1336 30 31, g32p_row07_traceSegment_075_1336_0030, g32p_row07_traceSegment_075_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1397 15 15, g32p_row07_traceSegment_075_1397_0015, g32p_row07_traceSegment_075_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1427 15 16, g32p_row07_traceSegment_075_1427_0015, g32p_row07_traceSegment_075_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1397 30 31, g32p_row07_traceSegment_075_1397_0030, g32p_row07_traceSegment_075_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_075 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1336 61 61, g32p_row07_traceSegment_075_1336_0061, g32p_row07_traceSegment_075_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_075 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1215 121 122, g32p_row07_traceSegment_075_1215_0121, g32p_row07_traceSegment_075_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_075 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 972 243 243, g32p_row07_traceSegment_075_0972_0243, g32p_row07_traceSegment_075_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1458 15 15, g32p_row07_traceSegment_075_1458_0015, g32p_row07_traceSegment_075_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1488 15 15, g32p_row07_traceSegment_075_1488_0015, g32p_row07_traceSegment_075_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_075 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1458 30 30, g32p_row07_traceSegment_075_1458_0030, g32p_row07_traceSegment_075_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1518 15 15, g32p_row07_traceSegment_075_1518_0015, g32p_row07_traceSegment_075_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1548 15 16, g32p_row07_traceSegment_075_1548_0015, g32p_row07_traceSegment_075_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1518 30 31, g32p_row07_traceSegment_075_1518_0030, g32p_row07_traceSegment_075_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_075 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1458 60 61, g32p_row07_traceSegment_075_1458_0060, g32p_row07_traceSegment_075_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1579 15 15, g32p_row07_traceSegment_075_1579_0015, g32p_row07_traceSegment_075_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1609 15 16, g32p_row07_traceSegment_075_1609_0015, g32p_row07_traceSegment_075_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1579 30 31, g32p_row07_traceSegment_075_1579_0030, g32p_row07_traceSegment_075_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1640 15 15, g32p_row07_traceSegment_075_1640_0015, g32p_row07_traceSegment_075_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1670 15 16, g32p_row07_traceSegment_075_1670_0015, g32p_row07_traceSegment_075_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1640 30 31, g32p_row07_traceSegment_075_1640_0030, g32p_row07_traceSegment_075_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_075 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1579 61 61, g32p_row07_traceSegment_075_1579_0061, g32p_row07_traceSegment_075_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_075 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1458 121 122, g32p_row07_traceSegment_075_1458_0121, g32p_row07_traceSegment_075_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1701 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1716 15 = [6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1701 30 = [7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1701 15 15, g32p_row07_traceSegment_075_1701_0015, g32p_row07_traceSegment_075_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1731 15 = [5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1731 30 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1731 15 15, g32p_row07_traceSegment_075_1731_0015, g32p_row07_traceSegment_075_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_075 1701 60 = [12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1701 30 30, g32p_row07_traceSegment_075_1701_0030, g32p_row07_traceSegment_075_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1761 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1761 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1761 15 15, g32p_row07_traceSegment_075_1761_0015, g32p_row07_traceSegment_075_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1791 15 16, g32p_row07_traceSegment_075_1791_0015, g32p_row07_traceSegment_075_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1761 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1761 30 31, g32p_row07_traceSegment_075_1761_0030, g32p_row07_traceSegment_075_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_075 1701 121 = [14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1701 60 61, g32p_row07_traceSegment_075_1701_0060, g32p_row07_traceSegment_075_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1837 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1822 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1822 15 15, g32p_row07_traceSegment_075_1822_0015, g32p_row07_traceSegment_075_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1852 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1867 16 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1852 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1852 15 16, g32p_row07_traceSegment_075_1852_0015, g32p_row07_traceSegment_075_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1822 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1822 30 31, g32p_row07_traceSegment_075_1822_0030, g32p_row07_traceSegment_075_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1883 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1898 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_075 1883 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1883 15 15, g32p_row07_traceSegment_075_1883_0015, g32p_row07_traceSegment_075_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_075 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_075 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_075_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_075 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1913 15 16, g32p_row07_traceSegment_075_1913_0015, g32p_row07_traceSegment_075_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_075 1883 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1883 30 31, g32p_row07_traceSegment_075_1883_0030, g32p_row07_traceSegment_075_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_075 1822 122 = [8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1822 61 61, g32p_row07_traceSegment_075_1822_0061, g32p_row07_traceSegment_075_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_075 1701 243 = [22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1701 121 122, g32p_row07_traceSegment_075_1701_0121, g32p_row07_traceSegment_075_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_075_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_075 1458 486 = [22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 1458 243 243, g32p_row07_traceSegment_075_1458_0243, g32p_row07_traceSegment_075_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_075 972 972 = [22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 972 486 486, g32p_row07_traceSegment_075_0972_0486, g32p_row07_traceSegment_075_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_075_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_075 0 1944 = [84] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_075 0 972 972, g32p_row07_traceSegment_075_0000_0972, g32p_row07_traceSegment_075_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 75 = [84] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_075_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_076 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 76 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_076_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 0 15 15, g32p_row07_traceSegment_076_0000_0015, g32p_row07_traceSegment_076_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 30 15 15, g32p_row07_traceSegment_076_0030_0015, g32p_row07_traceSegment_076_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_076 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 0 30 30, g32p_row07_traceSegment_076_0000_0030, g32p_row07_traceSegment_076_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 60 15 15, g32p_row07_traceSegment_076_0060_0015, g32p_row07_traceSegment_076_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 90 15 16, g32p_row07_traceSegment_076_0090_0015, g32p_row07_traceSegment_076_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 60 30 31, g32p_row07_traceSegment_076_0060_0030, g32p_row07_traceSegment_076_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_076 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 0 60 61, g32p_row07_traceSegment_076_0000_0060, g32p_row07_traceSegment_076_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 121 15 15, g32p_row07_traceSegment_076_0121_0015, g32p_row07_traceSegment_076_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 151 15 16, g32p_row07_traceSegment_076_0151_0015, g32p_row07_traceSegment_076_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 121 30 31, g32p_row07_traceSegment_076_0121_0030, g32p_row07_traceSegment_076_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 182 15 15, g32p_row07_traceSegment_076_0182_0015, g32p_row07_traceSegment_076_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 212 15 16, g32p_row07_traceSegment_076_0212_0015, g32p_row07_traceSegment_076_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 182 30 31, g32p_row07_traceSegment_076_0182_0030, g32p_row07_traceSegment_076_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_076 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 121 61 61, g32p_row07_traceSegment_076_0121_0061, g32p_row07_traceSegment_076_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_076 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 0 121 122, g32p_row07_traceSegment_076_0000_0121, g32p_row07_traceSegment_076_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 243 15 15, g32p_row07_traceSegment_076_0243_0015, g32p_row07_traceSegment_076_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 273 15 15, g32p_row07_traceSegment_076_0273_0015, g32p_row07_traceSegment_076_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_076 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 243 30 30, g32p_row07_traceSegment_076_0243_0030, g32p_row07_traceSegment_076_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 303 15 15, g32p_row07_traceSegment_076_0303_0015, g32p_row07_traceSegment_076_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 333 15 16, g32p_row07_traceSegment_076_0333_0015, g32p_row07_traceSegment_076_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 303 30 31, g32p_row07_traceSegment_076_0303_0030, g32p_row07_traceSegment_076_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_076 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 243 60 61, g32p_row07_traceSegment_076_0243_0060, g32p_row07_traceSegment_076_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 379 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 364 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 364 15 15, g32p_row07_traceSegment_076_0364_0015, g32p_row07_traceSegment_076_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 394 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 394 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 394 15 16, g32p_row07_traceSegment_076_0394_0015, g32p_row07_traceSegment_076_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 364 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 364 30 31, g32p_row07_traceSegment_076_0364_0030, g32p_row07_traceSegment_076_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 425 15 15, g32p_row07_traceSegment_076_0425_0015, g32p_row07_traceSegment_076_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 455 15 16, g32p_row07_traceSegment_076_0455_0015, g32p_row07_traceSegment_076_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 425 30 31, g32p_row07_traceSegment_076_0425_0030, g32p_row07_traceSegment_076_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_076 364 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 364 61 61, g32p_row07_traceSegment_076_0364_0061, g32p_row07_traceSegment_076_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_076 243 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 243 121 122, g32p_row07_traceSegment_076_0243_0121, g32p_row07_traceSegment_076_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_076 0 486 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 0 243 243, g32p_row07_traceSegment_076_0000_0243, g32p_row07_traceSegment_076_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 486 15 15, g32p_row07_traceSegment_076_0486_0015, g32p_row07_traceSegment_076_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 516 15 15, g32p_row07_traceSegment_076_0516_0015, g32p_row07_traceSegment_076_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_076 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 486 30 30, g32p_row07_traceSegment_076_0486_0030, g32p_row07_traceSegment_076_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 546 15 15, g32p_row07_traceSegment_076_0546_0015, g32p_row07_traceSegment_076_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 576 15 16, g32p_row07_traceSegment_076_0576_0015, g32p_row07_traceSegment_076_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 546 30 31, g32p_row07_traceSegment_076_0546_0030, g32p_row07_traceSegment_076_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_076 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 486 60 61, g32p_row07_traceSegment_076_0486_0060, g32p_row07_traceSegment_076_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 607 15 15, g32p_row07_traceSegment_076_0607_0015, g32p_row07_traceSegment_076_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 637 15 16, g32p_row07_traceSegment_076_0637_0015, g32p_row07_traceSegment_076_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 607 30 31, g32p_row07_traceSegment_076_0607_0030, g32p_row07_traceSegment_076_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 668 15 15, g32p_row07_traceSegment_076_0668_0015, g32p_row07_traceSegment_076_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 698 15 16, g32p_row07_traceSegment_076_0698_0015, g32p_row07_traceSegment_076_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 668 30 31, g32p_row07_traceSegment_076_0668_0030, g32p_row07_traceSegment_076_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_076 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 607 61 61, g32p_row07_traceSegment_076_0607_0061, g32p_row07_traceSegment_076_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_076 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 486 121 122, g32p_row07_traceSegment_076_0486_0121, g32p_row07_traceSegment_076_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 729 15 15, g32p_row07_traceSegment_076_0729_0015, g32p_row07_traceSegment_076_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 759 15 15, g32p_row07_traceSegment_076_0759_0015, g32p_row07_traceSegment_076_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_076 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 729 30 30, g32p_row07_traceSegment_076_0729_0030, g32p_row07_traceSegment_076_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 789 15 15, g32p_row07_traceSegment_076_0789_0015, g32p_row07_traceSegment_076_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 819 15 16, g32p_row07_traceSegment_076_0819_0015, g32p_row07_traceSegment_076_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 789 30 31, g32p_row07_traceSegment_076_0789_0030, g32p_row07_traceSegment_076_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_076 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 729 60 61, g32p_row07_traceSegment_076_0729_0060, g32p_row07_traceSegment_076_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 850 15 15, g32p_row07_traceSegment_076_0850_0015, g32p_row07_traceSegment_076_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 880 15 16, g32p_row07_traceSegment_076_0880_0015, g32p_row07_traceSegment_076_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 850 30 31, g32p_row07_traceSegment_076_0850_0030, g32p_row07_traceSegment_076_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 911 15 15, g32p_row07_traceSegment_076_0911_0015, g32p_row07_traceSegment_076_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 941 15 16, g32p_row07_traceSegment_076_0941_0015, g32p_row07_traceSegment_076_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 911 30 31, g32p_row07_traceSegment_076_0911_0030, g32p_row07_traceSegment_076_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_076 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 850 61 61, g32p_row07_traceSegment_076_0850_0061, g32p_row07_traceSegment_076_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_076 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 729 121 122, g32p_row07_traceSegment_076_0729_0121, g32p_row07_traceSegment_076_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_076 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 486 243 243, g32p_row07_traceSegment_076_0486_0243, g32p_row07_traceSegment_076_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_076 0 972 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 0 486 486, g32p_row07_traceSegment_076_0000_0486, g32p_row07_traceSegment_076_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 972 15 15, g32p_row07_traceSegment_076_0972_0015, g32p_row07_traceSegment_076_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1002 15 15, g32p_row07_traceSegment_076_1002_0015, g32p_row07_traceSegment_076_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_076 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 972 30 30, g32p_row07_traceSegment_076_0972_0030, g32p_row07_traceSegment_076_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1032 15 15, g32p_row07_traceSegment_076_1032_0015, g32p_row07_traceSegment_076_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1062 15 16, g32p_row07_traceSegment_076_1062_0015, g32p_row07_traceSegment_076_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1032 30 31, g32p_row07_traceSegment_076_1032_0030, g32p_row07_traceSegment_076_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_076 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 972 60 61, g32p_row07_traceSegment_076_0972_0060, g32p_row07_traceSegment_076_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1093 15 15, g32p_row07_traceSegment_076_1093_0015, g32p_row07_traceSegment_076_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1123 15 16, g32p_row07_traceSegment_076_1123_0015, g32p_row07_traceSegment_076_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1093 30 31, g32p_row07_traceSegment_076_1093_0030, g32p_row07_traceSegment_076_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1154 15 15, g32p_row07_traceSegment_076_1154_0015, g32p_row07_traceSegment_076_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1184 15 16, g32p_row07_traceSegment_076_1184_0015, g32p_row07_traceSegment_076_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1154 30 31, g32p_row07_traceSegment_076_1154_0030, g32p_row07_traceSegment_076_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_076 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1093 61 61, g32p_row07_traceSegment_076_1093_0061, g32p_row07_traceSegment_076_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_076 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 972 121 122, g32p_row07_traceSegment_076_0972_0121, g32p_row07_traceSegment_076_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1215 15 15, g32p_row07_traceSegment_076_1215_0015, g32p_row07_traceSegment_076_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1245 15 15, g32p_row07_traceSegment_076_1245_0015, g32p_row07_traceSegment_076_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_076 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1215 30 30, g32p_row07_traceSegment_076_1215_0030, g32p_row07_traceSegment_076_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1275 15 15, g32p_row07_traceSegment_076_1275_0015, g32p_row07_traceSegment_076_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1305 15 16, g32p_row07_traceSegment_076_1305_0015, g32p_row07_traceSegment_076_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1275 30 31, g32p_row07_traceSegment_076_1275_0030, g32p_row07_traceSegment_076_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_076 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1215 60 61, g32p_row07_traceSegment_076_1215_0060, g32p_row07_traceSegment_076_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1336 15 15, g32p_row07_traceSegment_076_1336_0015, g32p_row07_traceSegment_076_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1366 15 16, g32p_row07_traceSegment_076_1366_0015, g32p_row07_traceSegment_076_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1336 30 31, g32p_row07_traceSegment_076_1336_0030, g32p_row07_traceSegment_076_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1397 15 15, g32p_row07_traceSegment_076_1397_0015, g32p_row07_traceSegment_076_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1427 15 16, g32p_row07_traceSegment_076_1427_0015, g32p_row07_traceSegment_076_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1397 30 31, g32p_row07_traceSegment_076_1397_0030, g32p_row07_traceSegment_076_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_076 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1336 61 61, g32p_row07_traceSegment_076_1336_0061, g32p_row07_traceSegment_076_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_076 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1215 121 122, g32p_row07_traceSegment_076_1215_0121, g32p_row07_traceSegment_076_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_076 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 972 243 243, g32p_row07_traceSegment_076_0972_0243, g32p_row07_traceSegment_076_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1458 15 15, g32p_row07_traceSegment_076_1458_0015, g32p_row07_traceSegment_076_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1488 15 15, g32p_row07_traceSegment_076_1488_0015, g32p_row07_traceSegment_076_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_076 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1458 30 30, g32p_row07_traceSegment_076_1458_0030, g32p_row07_traceSegment_076_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1518 15 15, g32p_row07_traceSegment_076_1518_0015, g32p_row07_traceSegment_076_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1548 15 16, g32p_row07_traceSegment_076_1548_0015, g32p_row07_traceSegment_076_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1518 30 31, g32p_row07_traceSegment_076_1518_0030, g32p_row07_traceSegment_076_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_076 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1458 60 61, g32p_row07_traceSegment_076_1458_0060, g32p_row07_traceSegment_076_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1579 15 15, g32p_row07_traceSegment_076_1579_0015, g32p_row07_traceSegment_076_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1609 15 16, g32p_row07_traceSegment_076_1609_0015, g32p_row07_traceSegment_076_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1579 30 31, g32p_row07_traceSegment_076_1579_0030, g32p_row07_traceSegment_076_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1640 15 15, g32p_row07_traceSegment_076_1640_0015, g32p_row07_traceSegment_076_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1670 15 16, g32p_row07_traceSegment_076_1670_0015, g32p_row07_traceSegment_076_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1640 30 31, g32p_row07_traceSegment_076_1640_0030, g32p_row07_traceSegment_076_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_076 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1579 61 61, g32p_row07_traceSegment_076_1579_0061, g32p_row07_traceSegment_076_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_076 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1458 121 122, g32p_row07_traceSegment_076_1458_0121, g32p_row07_traceSegment_076_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1701 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1701 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1701 15 15, g32p_row07_traceSegment_076_1701_0015, g32p_row07_traceSegment_076_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1731 15 15, g32p_row07_traceSegment_076_1731_0015, g32p_row07_traceSegment_076_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_076 1701 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1701 30 30, g32p_row07_traceSegment_076_1701_0030, g32p_row07_traceSegment_076_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1761 15 15, g32p_row07_traceSegment_076_1761_0015, g32p_row07_traceSegment_076_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1791 15 16, g32p_row07_traceSegment_076_1791_0015, g32p_row07_traceSegment_076_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1761 30 31, g32p_row07_traceSegment_076_1761_0030, g32p_row07_traceSegment_076_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_076 1701 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1701 60 61, g32p_row07_traceSegment_076_1701_0060, g32p_row07_traceSegment_076_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1822 15 15, g32p_row07_traceSegment_076_1822_0015, g32p_row07_traceSegment_076_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1852 15 16, g32p_row07_traceSegment_076_1852_0015, g32p_row07_traceSegment_076_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1822 30 31, g32p_row07_traceSegment_076_1822_0030, g32p_row07_traceSegment_076_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_076 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1883 15 15, g32p_row07_traceSegment_076_1883_0015, g32p_row07_traceSegment_076_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_076 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_076 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_076_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_076 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1913 15 16, g32p_row07_traceSegment_076_1913_0015, g32p_row07_traceSegment_076_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_076 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1883 30 31, g32p_row07_traceSegment_076_1883_0030, g32p_row07_traceSegment_076_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_076 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1822 61 61, g32p_row07_traceSegment_076_1822_0061, g32p_row07_traceSegment_076_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_076 1701 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1701 121 122, g32p_row07_traceSegment_076_1701_0121, g32p_row07_traceSegment_076_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_076_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_076 1458 486 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 1458 243 243, g32p_row07_traceSegment_076_1458_0243, g32p_row07_traceSegment_076_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_076 972 972 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 972 486 486, g32p_row07_traceSegment_076_0972_0486, g32p_row07_traceSegment_076_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_076_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_076 0 1944 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_076 0 972 972, g32p_row07_traceSegment_076_0000_0972, g32p_row07_traceSegment_076_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 76 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_076_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_078 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 78 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_078_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 0 15 15, g32p_row07_traceSegment_078_0000_0015, g32p_row07_traceSegment_078_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 30 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 30 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 30 15 15, g32p_row07_traceSegment_078_0030_0015, g32p_row07_traceSegment_078_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_078 0 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 0 30 30, g32p_row07_traceSegment_078_0000_0030, g32p_row07_traceSegment_078_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 60 15 15, g32p_row07_traceSegment_078_0060_0015, g32p_row07_traceSegment_078_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 90 15 16, g32p_row07_traceSegment_078_0090_0015, g32p_row07_traceSegment_078_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 60 30 31, g32p_row07_traceSegment_078_0060_0030, g32p_row07_traceSegment_078_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_078 0 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 0 60 61, g32p_row07_traceSegment_078_0000_0060, g32p_row07_traceSegment_078_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 121 15 15, g32p_row07_traceSegment_078_0121_0015, g32p_row07_traceSegment_078_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 151 15 16, g32p_row07_traceSegment_078_0151_0015, g32p_row07_traceSegment_078_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 121 30 31, g32p_row07_traceSegment_078_0121_0030, g32p_row07_traceSegment_078_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 182 15 15, g32p_row07_traceSegment_078_0182_0015, g32p_row07_traceSegment_078_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 212 15 16, g32p_row07_traceSegment_078_0212_0015, g32p_row07_traceSegment_078_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 182 30 31, g32p_row07_traceSegment_078_0182_0030, g32p_row07_traceSegment_078_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_078 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 121 61 61, g32p_row07_traceSegment_078_0121_0061, g32p_row07_traceSegment_078_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_078 0 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 0 121 122, g32p_row07_traceSegment_078_0000_0121, g32p_row07_traceSegment_078_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 243 15 15, g32p_row07_traceSegment_078_0243_0015, g32p_row07_traceSegment_078_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 273 15 15, g32p_row07_traceSegment_078_0273_0015, g32p_row07_traceSegment_078_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_078 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 243 30 30, g32p_row07_traceSegment_078_0243_0030, g32p_row07_traceSegment_078_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 303 15 15, g32p_row07_traceSegment_078_0303_0015, g32p_row07_traceSegment_078_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 333 15 16, g32p_row07_traceSegment_078_0333_0015, g32p_row07_traceSegment_078_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 303 30 31, g32p_row07_traceSegment_078_0303_0030, g32p_row07_traceSegment_078_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_078 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 243 60 61, g32p_row07_traceSegment_078_0243_0060, g32p_row07_traceSegment_078_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 379 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 364 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 364 15 15, g32p_row07_traceSegment_078_0364_0015, g32p_row07_traceSegment_078_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 394 15 16, g32p_row07_traceSegment_078_0394_0015, g32p_row07_traceSegment_078_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 364 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 364 30 31, g32p_row07_traceSegment_078_0364_0030, g32p_row07_traceSegment_078_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 425 15 15, g32p_row07_traceSegment_078_0425_0015, g32p_row07_traceSegment_078_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 455 15 16, g32p_row07_traceSegment_078_0455_0015, g32p_row07_traceSegment_078_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 425 30 31, g32p_row07_traceSegment_078_0425_0030, g32p_row07_traceSegment_078_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_078 364 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 364 61 61, g32p_row07_traceSegment_078_0364_0061, g32p_row07_traceSegment_078_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_078 243 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 243 121 122, g32p_row07_traceSegment_078_0243_0121, g32p_row07_traceSegment_078_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_078 0 486 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 0 243 243, g32p_row07_traceSegment_078_0000_0243, g32p_row07_traceSegment_078_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 486 15 15, g32p_row07_traceSegment_078_0486_0015, g32p_row07_traceSegment_078_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 516 15 15, g32p_row07_traceSegment_078_0516_0015, g32p_row07_traceSegment_078_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_078 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 486 30 30, g32p_row07_traceSegment_078_0486_0030, g32p_row07_traceSegment_078_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 546 15 15, g32p_row07_traceSegment_078_0546_0015, g32p_row07_traceSegment_078_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 576 15 16, g32p_row07_traceSegment_078_0576_0015, g32p_row07_traceSegment_078_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 546 30 31, g32p_row07_traceSegment_078_0546_0030, g32p_row07_traceSegment_078_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_078 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 486 60 61, g32p_row07_traceSegment_078_0486_0060, g32p_row07_traceSegment_078_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 622 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 607 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 607 15 15, g32p_row07_traceSegment_078_0607_0015, g32p_row07_traceSegment_078_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 637 15 16, g32p_row07_traceSegment_078_0637_0015, g32p_row07_traceSegment_078_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 607 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 607 30 31, g32p_row07_traceSegment_078_0607_0030, g32p_row07_traceSegment_078_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 668 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 668 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 668 15 15, g32p_row07_traceSegment_078_0668_0015, g32p_row07_traceSegment_078_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 698 15 16, g32p_row07_traceSegment_078_0698_0015, g32p_row07_traceSegment_078_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 668 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 668 30 31, g32p_row07_traceSegment_078_0668_0030, g32p_row07_traceSegment_078_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_078 607 122 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 607 61 61, g32p_row07_traceSegment_078_0607_0061, g32p_row07_traceSegment_078_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_078 486 243 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 486 121 122, g32p_row07_traceSegment_078_0486_0121, g32p_row07_traceSegment_078_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 729 15 15, g32p_row07_traceSegment_078_0729_0015, g32p_row07_traceSegment_078_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 759 15 15, g32p_row07_traceSegment_078_0759_0015, g32p_row07_traceSegment_078_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_078 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 729 30 30, g32p_row07_traceSegment_078_0729_0030, g32p_row07_traceSegment_078_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 789 15 15, g32p_row07_traceSegment_078_0789_0015, g32p_row07_traceSegment_078_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 819 15 16, g32p_row07_traceSegment_078_0819_0015, g32p_row07_traceSegment_078_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 789 30 31, g32p_row07_traceSegment_078_0789_0030, g32p_row07_traceSegment_078_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_078 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 729 60 61, g32p_row07_traceSegment_078_0729_0060, g32p_row07_traceSegment_078_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 850 15 15, g32p_row07_traceSegment_078_0850_0015, g32p_row07_traceSegment_078_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 880 15 16, g32p_row07_traceSegment_078_0880_0015, g32p_row07_traceSegment_078_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 850 30 31, g32p_row07_traceSegment_078_0850_0030, g32p_row07_traceSegment_078_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 911 15 15, g32p_row07_traceSegment_078_0911_0015, g32p_row07_traceSegment_078_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 941 15 16, g32p_row07_traceSegment_078_0941_0015, g32p_row07_traceSegment_078_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 911 30 31, g32p_row07_traceSegment_078_0911_0030, g32p_row07_traceSegment_078_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_078 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 850 61 61, g32p_row07_traceSegment_078_0850_0061, g32p_row07_traceSegment_078_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_078 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 729 121 122, g32p_row07_traceSegment_078_0729_0121, g32p_row07_traceSegment_078_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_078 486 486 = [3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 486 243 243, g32p_row07_traceSegment_078_0486_0243, g32p_row07_traceSegment_078_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_078 0 972 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 0 486 486, g32p_row07_traceSegment_078_0000_0486, g32p_row07_traceSegment_078_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 972 15 15, g32p_row07_traceSegment_078_0972_0015, g32p_row07_traceSegment_078_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1002 15 15, g32p_row07_traceSegment_078_1002_0015, g32p_row07_traceSegment_078_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_078 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 972 30 30, g32p_row07_traceSegment_078_0972_0030, g32p_row07_traceSegment_078_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1032 15 15, g32p_row07_traceSegment_078_1032_0015, g32p_row07_traceSegment_078_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1062 15 16, g32p_row07_traceSegment_078_1062_0015, g32p_row07_traceSegment_078_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1032 30 31, g32p_row07_traceSegment_078_1032_0030, g32p_row07_traceSegment_078_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_078 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 972 60 61, g32p_row07_traceSegment_078_0972_0060, g32p_row07_traceSegment_078_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1093 15 15, g32p_row07_traceSegment_078_1093_0015, g32p_row07_traceSegment_078_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1123 15 16, g32p_row07_traceSegment_078_1123_0015, g32p_row07_traceSegment_078_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1093 30 31, g32p_row07_traceSegment_078_1093_0030, g32p_row07_traceSegment_078_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1154 15 15, g32p_row07_traceSegment_078_1154_0015, g32p_row07_traceSegment_078_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1184 15 16, g32p_row07_traceSegment_078_1184_0015, g32p_row07_traceSegment_078_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1154 30 31, g32p_row07_traceSegment_078_1154_0030, g32p_row07_traceSegment_078_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_078 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1093 61 61, g32p_row07_traceSegment_078_1093_0061, g32p_row07_traceSegment_078_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_078 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 972 121 122, g32p_row07_traceSegment_078_0972_0121, g32p_row07_traceSegment_078_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1215 15 15, g32p_row07_traceSegment_078_1215_0015, g32p_row07_traceSegment_078_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1245 15 15, g32p_row07_traceSegment_078_1245_0015, g32p_row07_traceSegment_078_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_078 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1215 30 30, g32p_row07_traceSegment_078_1215_0030, g32p_row07_traceSegment_078_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1275 15 15, g32p_row07_traceSegment_078_1275_0015, g32p_row07_traceSegment_078_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1305 15 16, g32p_row07_traceSegment_078_1305_0015, g32p_row07_traceSegment_078_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1275 30 31, g32p_row07_traceSegment_078_1275_0030, g32p_row07_traceSegment_078_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_078 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1215 60 61, g32p_row07_traceSegment_078_1215_0060, g32p_row07_traceSegment_078_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1336 15 15, g32p_row07_traceSegment_078_1336_0015, g32p_row07_traceSegment_078_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1366 15 16, g32p_row07_traceSegment_078_1366_0015, g32p_row07_traceSegment_078_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1336 30 31, g32p_row07_traceSegment_078_1336_0030, g32p_row07_traceSegment_078_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1397 15 15, g32p_row07_traceSegment_078_1397_0015, g32p_row07_traceSegment_078_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1427 15 16, g32p_row07_traceSegment_078_1427_0015, g32p_row07_traceSegment_078_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1397 30 31, g32p_row07_traceSegment_078_1397_0030, g32p_row07_traceSegment_078_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_078 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1336 61 61, g32p_row07_traceSegment_078_1336_0061, g32p_row07_traceSegment_078_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_078 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1215 121 122, g32p_row07_traceSegment_078_1215_0121, g32p_row07_traceSegment_078_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_078 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 972 243 243, g32p_row07_traceSegment_078_0972_0243, g32p_row07_traceSegment_078_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1458 15 15, g32p_row07_traceSegment_078_1458_0015, g32p_row07_traceSegment_078_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1488 15 15, g32p_row07_traceSegment_078_1488_0015, g32p_row07_traceSegment_078_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_078 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1458 30 30, g32p_row07_traceSegment_078_1458_0030, g32p_row07_traceSegment_078_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1518 15 15, g32p_row07_traceSegment_078_1518_0015, g32p_row07_traceSegment_078_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1548 15 16, g32p_row07_traceSegment_078_1548_0015, g32p_row07_traceSegment_078_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1518 30 31, g32p_row07_traceSegment_078_1518_0030, g32p_row07_traceSegment_078_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_078 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1458 60 61, g32p_row07_traceSegment_078_1458_0060, g32p_row07_traceSegment_078_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1579 15 15, g32p_row07_traceSegment_078_1579_0015, g32p_row07_traceSegment_078_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1609 15 16, g32p_row07_traceSegment_078_1609_0015, g32p_row07_traceSegment_078_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1579 30 31, g32p_row07_traceSegment_078_1579_0030, g32p_row07_traceSegment_078_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1640 15 15, g32p_row07_traceSegment_078_1640_0015, g32p_row07_traceSegment_078_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1670 15 16, g32p_row07_traceSegment_078_1670_0015, g32p_row07_traceSegment_078_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1640 30 31, g32p_row07_traceSegment_078_1640_0030, g32p_row07_traceSegment_078_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_078 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1579 61 61, g32p_row07_traceSegment_078_1579_0061, g32p_row07_traceSegment_078_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_078 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1458 121 122, g32p_row07_traceSegment_078_1458_0121, g32p_row07_traceSegment_078_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1701 15 15, g32p_row07_traceSegment_078_1701_0015, g32p_row07_traceSegment_078_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1731 15 15, g32p_row07_traceSegment_078_1731_0015, g32p_row07_traceSegment_078_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_078 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1701 30 30, g32p_row07_traceSegment_078_1701_0030, g32p_row07_traceSegment_078_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1761 15 15, g32p_row07_traceSegment_078_1761_0015, g32p_row07_traceSegment_078_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1791 15 16, g32p_row07_traceSegment_078_1791_0015, g32p_row07_traceSegment_078_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1761 30 31, g32p_row07_traceSegment_078_1761_0030, g32p_row07_traceSegment_078_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_078 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1701 60 61, g32p_row07_traceSegment_078_1701_0060, g32p_row07_traceSegment_078_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1822 15 15, g32p_row07_traceSegment_078_1822_0015, g32p_row07_traceSegment_078_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1852 15 16, g32p_row07_traceSegment_078_1852_0015, g32p_row07_traceSegment_078_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1822 30 31, g32p_row07_traceSegment_078_1822_0030, g32p_row07_traceSegment_078_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_078 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1883 15 15, g32p_row07_traceSegment_078_1883_0015, g32p_row07_traceSegment_078_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_078 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_078 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_078_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_078 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1913 15 16, g32p_row07_traceSegment_078_1913_0015, g32p_row07_traceSegment_078_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_078 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1883 30 31, g32p_row07_traceSegment_078_1883_0030, g32p_row07_traceSegment_078_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_078 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1822 61 61, g32p_row07_traceSegment_078_1822_0061, g32p_row07_traceSegment_078_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_078 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1701 121 122, g32p_row07_traceSegment_078_1701_0121, g32p_row07_traceSegment_078_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_078_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_078 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 1458 243 243, g32p_row07_traceSegment_078_1458_0243, g32p_row07_traceSegment_078_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_078 972 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 972 486 486, g32p_row07_traceSegment_078_0972_0486, g32p_row07_traceSegment_078_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_078_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_078 0 1944 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_078 0 972 972, g32p_row07_traceSegment_078_0000_0972, g32p_row07_traceSegment_078_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 78 = [6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_078_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_084 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 84 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_084_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 0 15 15, g32p_row07_traceSegment_084_0000_0015, g32p_row07_traceSegment_084_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 30 15 15, g32p_row07_traceSegment_084_0030_0015, g32p_row07_traceSegment_084_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_084 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 0 30 30, g32p_row07_traceSegment_084_0000_0030, g32p_row07_traceSegment_084_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 60 15 15, g32p_row07_traceSegment_084_0060_0015, g32p_row07_traceSegment_084_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 90 15 16, g32p_row07_traceSegment_084_0090_0015, g32p_row07_traceSegment_084_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 60 30 31, g32p_row07_traceSegment_084_0060_0030, g32p_row07_traceSegment_084_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_084 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 0 60 61, g32p_row07_traceSegment_084_0000_0060, g32p_row07_traceSegment_084_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 121 15 15, g32p_row07_traceSegment_084_0121_0015, g32p_row07_traceSegment_084_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 166 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 151 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 151 15 16, g32p_row07_traceSegment_084_0151_0015, g32p_row07_traceSegment_084_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 121 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 121 30 31, g32p_row07_traceSegment_084_0121_0030, g32p_row07_traceSegment_084_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 182 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 197 15 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 182 30 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 182 15 15, g32p_row07_traceSegment_084_0182_0015, g32p_row07_traceSegment_084_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 212 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 227 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 212 31 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 212 15 16, g32p_row07_traceSegment_084_0212_0015, g32p_row07_traceSegment_084_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 182 61 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 182 30 31, g32p_row07_traceSegment_084_0182_0030, g32p_row07_traceSegment_084_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_084 121 122 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 121 61 61, g32p_row07_traceSegment_084_0121_0061, g32p_row07_traceSegment_084_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_084 0 243 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 0 121 122, g32p_row07_traceSegment_084_0000_0121, g32p_row07_traceSegment_084_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 243 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 258 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 243 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 243 15 15, g32p_row07_traceSegment_084_0243_0015, g32p_row07_traceSegment_084_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 288 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 273 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 273 15 15, g32p_row07_traceSegment_084_0273_0015, g32p_row07_traceSegment_084_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_084 243 60 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 243 30 30, g32p_row07_traceSegment_084_0243_0030, g32p_row07_traceSegment_084_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 303 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 318 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 303 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 303 15 15, g32p_row07_traceSegment_084_0303_0015, g32p_row07_traceSegment_084_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 333 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 348 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 333 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 333 15 16, g32p_row07_traceSegment_084_0333_0015, g32p_row07_traceSegment_084_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 303 61 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 303 30 31, g32p_row07_traceSegment_084_0303_0030, g32p_row07_traceSegment_084_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_084 243 121 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 243 60 61, g32p_row07_traceSegment_084_0243_0060, g32p_row07_traceSegment_084_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 364 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 364 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 364 15 15, g32p_row07_traceSegment_084_0364_0015, g32p_row07_traceSegment_084_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 394 15 16, g32p_row07_traceSegment_084_0394_0015, g32p_row07_traceSegment_084_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 364 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 364 30 31, g32p_row07_traceSegment_084_0364_0030, g32p_row07_traceSegment_084_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 425 15 15, g32p_row07_traceSegment_084_0425_0015, g32p_row07_traceSegment_084_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 455 15 16, g32p_row07_traceSegment_084_0455_0015, g32p_row07_traceSegment_084_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 425 30 31, g32p_row07_traceSegment_084_0425_0030, g32p_row07_traceSegment_084_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_084 364 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 364 61 61, g32p_row07_traceSegment_084_0364_0061, g32p_row07_traceSegment_084_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_084 243 243 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 243 121 122, g32p_row07_traceSegment_084_0243_0121, g32p_row07_traceSegment_084_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_084 0 486 = [0, 34] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 0 243 243, g32p_row07_traceSegment_084_0000_0243, g32p_row07_traceSegment_084_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 486 15 15, g32p_row07_traceSegment_084_0486_0015, g32p_row07_traceSegment_084_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 516 15 15, g32p_row07_traceSegment_084_0516_0015, g32p_row07_traceSegment_084_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_084 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 486 30 30, g32p_row07_traceSegment_084_0486_0030, g32p_row07_traceSegment_084_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 546 15 15, g32p_row07_traceSegment_084_0546_0015, g32p_row07_traceSegment_084_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 576 15 16, g32p_row07_traceSegment_084_0576_0015, g32p_row07_traceSegment_084_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 546 30 31, g32p_row07_traceSegment_084_0546_0030, g32p_row07_traceSegment_084_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_084 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 486 60 61, g32p_row07_traceSegment_084_0486_0060, g32p_row07_traceSegment_084_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 607 15 15, g32p_row07_traceSegment_084_0607_0015, g32p_row07_traceSegment_084_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 637 15 16, g32p_row07_traceSegment_084_0637_0015, g32p_row07_traceSegment_084_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 607 30 31, g32p_row07_traceSegment_084_0607_0030, g32p_row07_traceSegment_084_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 668 15 15, g32p_row07_traceSegment_084_0668_0015, g32p_row07_traceSegment_084_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 698 15 16, g32p_row07_traceSegment_084_0698_0015, g32p_row07_traceSegment_084_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 668 30 31, g32p_row07_traceSegment_084_0668_0030, g32p_row07_traceSegment_084_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_084 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 607 61 61, g32p_row07_traceSegment_084_0607_0061, g32p_row07_traceSegment_084_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_084 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 486 121 122, g32p_row07_traceSegment_084_0486_0121, g32p_row07_traceSegment_084_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 729 15 15, g32p_row07_traceSegment_084_0729_0015, g32p_row07_traceSegment_084_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 759 15 15, g32p_row07_traceSegment_084_0759_0015, g32p_row07_traceSegment_084_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_084 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 729 30 30, g32p_row07_traceSegment_084_0729_0030, g32p_row07_traceSegment_084_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 789 15 15, g32p_row07_traceSegment_084_0789_0015, g32p_row07_traceSegment_084_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 819 15 16, g32p_row07_traceSegment_084_0819_0015, g32p_row07_traceSegment_084_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 789 30 31, g32p_row07_traceSegment_084_0789_0030, g32p_row07_traceSegment_084_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_084 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 729 60 61, g32p_row07_traceSegment_084_0729_0060, g32p_row07_traceSegment_084_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 850 15 15, g32p_row07_traceSegment_084_0850_0015, g32p_row07_traceSegment_084_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 880 15 16, g32p_row07_traceSegment_084_0880_0015, g32p_row07_traceSegment_084_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 850 30 31, g32p_row07_traceSegment_084_0850_0030, g32p_row07_traceSegment_084_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 911 15 15, g32p_row07_traceSegment_084_0911_0015, g32p_row07_traceSegment_084_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 941 15 16, g32p_row07_traceSegment_084_0941_0015, g32p_row07_traceSegment_084_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 911 30 31, g32p_row07_traceSegment_084_0911_0030, g32p_row07_traceSegment_084_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_084 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 850 61 61, g32p_row07_traceSegment_084_0850_0061, g32p_row07_traceSegment_084_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_084 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 729 121 122, g32p_row07_traceSegment_084_0729_0121, g32p_row07_traceSegment_084_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_084 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 486 243 243, g32p_row07_traceSegment_084_0486_0243, g32p_row07_traceSegment_084_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_084 0 972 = [0, 34] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 0 486 486, g32p_row07_traceSegment_084_0000_0486, g32p_row07_traceSegment_084_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 972 15 15, g32p_row07_traceSegment_084_0972_0015, g32p_row07_traceSegment_084_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1002 15 15, g32p_row07_traceSegment_084_1002_0015, g32p_row07_traceSegment_084_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_084 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 972 30 30, g32p_row07_traceSegment_084_0972_0030, g32p_row07_traceSegment_084_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1032 15 15, g32p_row07_traceSegment_084_1032_0015, g32p_row07_traceSegment_084_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1062 15 16, g32p_row07_traceSegment_084_1062_0015, g32p_row07_traceSegment_084_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1032 30 31, g32p_row07_traceSegment_084_1032_0030, g32p_row07_traceSegment_084_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_084 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 972 60 61, g32p_row07_traceSegment_084_0972_0060, g32p_row07_traceSegment_084_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1093 15 15, g32p_row07_traceSegment_084_1093_0015, g32p_row07_traceSegment_084_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1123 15 16, g32p_row07_traceSegment_084_1123_0015, g32p_row07_traceSegment_084_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1093 30 31, g32p_row07_traceSegment_084_1093_0030, g32p_row07_traceSegment_084_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1154 15 15, g32p_row07_traceSegment_084_1154_0015, g32p_row07_traceSegment_084_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1184 15 16, g32p_row07_traceSegment_084_1184_0015, g32p_row07_traceSegment_084_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1154 30 31, g32p_row07_traceSegment_084_1154_0030, g32p_row07_traceSegment_084_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_084 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1093 61 61, g32p_row07_traceSegment_084_1093_0061, g32p_row07_traceSegment_084_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_084 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 972 121 122, g32p_row07_traceSegment_084_0972_0121, g32p_row07_traceSegment_084_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1215 15 15, g32p_row07_traceSegment_084_1215_0015, g32p_row07_traceSegment_084_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1245 15 15, g32p_row07_traceSegment_084_1245_0015, g32p_row07_traceSegment_084_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_084 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1215 30 30, g32p_row07_traceSegment_084_1215_0030, g32p_row07_traceSegment_084_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1290 15 = [0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1275 30 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1275 15 15, g32p_row07_traceSegment_084_1275_0015, g32p_row07_traceSegment_084_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1305 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1305 31 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1305 15 16, g32p_row07_traceSegment_084_1305_0015, g32p_row07_traceSegment_084_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1275 61 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1275 30 31, g32p_row07_traceSegment_084_1275_0030, g32p_row07_traceSegment_084_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_084 1215 121 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1215 60 61, g32p_row07_traceSegment_084_1215_0060, g32p_row07_traceSegment_084_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1336 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1351 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1336 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1336 15 15, g32p_row07_traceSegment_084_1336_0015, g32p_row07_traceSegment_084_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1366 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1381 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1366 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1366 15 16, g32p_row07_traceSegment_084_1366_0015, g32p_row07_traceSegment_084_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1336 61 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1336 30 31, g32p_row07_traceSegment_084_1336_0030, g32p_row07_traceSegment_084_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1412 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1397 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1397 15 15, g32p_row07_traceSegment_084_1397_0015, g32p_row07_traceSegment_084_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1442 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1427 31 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1427 15 16, g32p_row07_traceSegment_084_1427_0015, g32p_row07_traceSegment_084_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1397 61 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1397 30 31, g32p_row07_traceSegment_084_1397_0030, g32p_row07_traceSegment_084_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_084 1336 122 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1336 61 61, g32p_row07_traceSegment_084_1336_0061, g32p_row07_traceSegment_084_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_084 1215 243 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1215 121 122, g32p_row07_traceSegment_084_1215_0121, g32p_row07_traceSegment_084_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_084 972 486 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 972 243 243, g32p_row07_traceSegment_084_0972_0243, g32p_row07_traceSegment_084_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1458 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1473 15 = [0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1458 30 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1458 15 15, g32p_row07_traceSegment_084_1458_0015, g32p_row07_traceSegment_084_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1488 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1503 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1488 30 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1488 15 15, g32p_row07_traceSegment_084_1488_0015, g32p_row07_traceSegment_084_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_084 1458 60 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1458 30 30, g32p_row07_traceSegment_084_1458_0030, g32p_row07_traceSegment_084_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1518 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1533 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1518 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1518 15 15, g32p_row07_traceSegment_084_1518_0015, g32p_row07_traceSegment_084_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1548 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1563 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1548 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1548 15 16, g32p_row07_traceSegment_084_1548_0015, g32p_row07_traceSegment_084_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1518 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1518 30 31, g32p_row07_traceSegment_084_1518_0030, g32p_row07_traceSegment_084_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_084 1458 121 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1458 60 61, g32p_row07_traceSegment_084_1458_0060, g32p_row07_traceSegment_084_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1579 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1594 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1579 30 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1579 15 15, g32p_row07_traceSegment_084_1579_0015, g32p_row07_traceSegment_084_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1609 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1609 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1609 15 16, g32p_row07_traceSegment_084_1609_0015, g32p_row07_traceSegment_084_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1579 61 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1579 30 31, g32p_row07_traceSegment_084_1579_0030, g32p_row07_traceSegment_084_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1640 15 15, g32p_row07_traceSegment_084_1640_0015, g32p_row07_traceSegment_084_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1685 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1670 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1670 15 16, g32p_row07_traceSegment_084_1670_0015, g32p_row07_traceSegment_084_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1640 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1640 30 31, g32p_row07_traceSegment_084_1640_0030, g32p_row07_traceSegment_084_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_084 1579 122 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1579 61 61, g32p_row07_traceSegment_084_1579_0061, g32p_row07_traceSegment_084_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_084 1458 243 = [0, 28] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1458 121 122, g32p_row07_traceSegment_084_1458_0121, g32p_row07_traceSegment_084_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1701 15 15, g32p_row07_traceSegment_084_1701_0015, g32p_row07_traceSegment_084_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1731 15 15, g32p_row07_traceSegment_084_1731_0015, g32p_row07_traceSegment_084_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_084 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1701 30 30, g32p_row07_traceSegment_084_1701_0030, g32p_row07_traceSegment_084_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1761 15 15, g32p_row07_traceSegment_084_1761_0015, g32p_row07_traceSegment_084_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1791 15 16, g32p_row07_traceSegment_084_1791_0015, g32p_row07_traceSegment_084_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1761 30 31, g32p_row07_traceSegment_084_1761_0030, g32p_row07_traceSegment_084_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_084 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1701 60 61, g32p_row07_traceSegment_084_1701_0060, g32p_row07_traceSegment_084_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1822 15 15, g32p_row07_traceSegment_084_1822_0015, g32p_row07_traceSegment_084_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1852 15 16, g32p_row07_traceSegment_084_1852_0015, g32p_row07_traceSegment_084_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1822 30 31, g32p_row07_traceSegment_084_1822_0030, g32p_row07_traceSegment_084_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_084 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1883 15 15, g32p_row07_traceSegment_084_1883_0015, g32p_row07_traceSegment_084_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_084 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_084 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_084_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_084 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1913 15 16, g32p_row07_traceSegment_084_1913_0015, g32p_row07_traceSegment_084_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_084 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1883 30 31, g32p_row07_traceSegment_084_1883_0030, g32p_row07_traceSegment_084_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_084 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1822 61 61, g32p_row07_traceSegment_084_1822_0061, g32p_row07_traceSegment_084_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_084 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1701 121 122, g32p_row07_traceSegment_084_1701_0121, g32p_row07_traceSegment_084_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_084_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_084 1458 486 = [0, 28] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 1458 243 243, g32p_row07_traceSegment_084_1458_0243, g32p_row07_traceSegment_084_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_084 972 972 = [0, 50] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 972 486 486, g32p_row07_traceSegment_084_0972_0486, g32p_row07_traceSegment_084_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_084_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_084 0 1944 = [0, 84] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_084 0 972 972, g32p_row07_traceSegment_084_0000_0972, g32p_row07_traceSegment_084_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 84 = [0, 84] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_084_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_087 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 87 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_087_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 0 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 0 15 15, g32p_row07_traceSegment_087_0000_0015, g32p_row07_traceSegment_087_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 30 15 15, g32p_row07_traceSegment_087_0030_0015, g32p_row07_traceSegment_087_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_087 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 0 30 30, g32p_row07_traceSegment_087_0000_0030, g32p_row07_traceSegment_087_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 60 15 15, g32p_row07_traceSegment_087_0060_0015, g32p_row07_traceSegment_087_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 90 15 16, g32p_row07_traceSegment_087_0090_0015, g32p_row07_traceSegment_087_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 60 30 31, g32p_row07_traceSegment_087_0060_0030, g32p_row07_traceSegment_087_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_087 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 0 60 61, g32p_row07_traceSegment_087_0000_0060, g32p_row07_traceSegment_087_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 121 15 15, g32p_row07_traceSegment_087_0121_0015, g32p_row07_traceSegment_087_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 151 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 151 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 151 15 16, g32p_row07_traceSegment_087_0151_0015, g32p_row07_traceSegment_087_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 121 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 121 30 31, g32p_row07_traceSegment_087_0121_0030, g32p_row07_traceSegment_087_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 182 15 15, g32p_row07_traceSegment_087_0182_0015, g32p_row07_traceSegment_087_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 212 15 16, g32p_row07_traceSegment_087_0212_0015, g32p_row07_traceSegment_087_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 182 30 31, g32p_row07_traceSegment_087_0182_0030, g32p_row07_traceSegment_087_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_087 121 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 121 61 61, g32p_row07_traceSegment_087_0121_0061, g32p_row07_traceSegment_087_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_087 0 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 0 121 122, g32p_row07_traceSegment_087_0000_0121, g32p_row07_traceSegment_087_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 243 15 15, g32p_row07_traceSegment_087_0243_0015, g32p_row07_traceSegment_087_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 273 15 15, g32p_row07_traceSegment_087_0273_0015, g32p_row07_traceSegment_087_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_087 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 243 30 30, g32p_row07_traceSegment_087_0243_0030, g32p_row07_traceSegment_087_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 303 15 15, g32p_row07_traceSegment_087_0303_0015, g32p_row07_traceSegment_087_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 333 15 16, g32p_row07_traceSegment_087_0333_0015, g32p_row07_traceSegment_087_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 303 30 31, g32p_row07_traceSegment_087_0303_0030, g32p_row07_traceSegment_087_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_087 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 243 60 61, g32p_row07_traceSegment_087_0243_0060, g32p_row07_traceSegment_087_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 364 15 15, g32p_row07_traceSegment_087_0364_0015, g32p_row07_traceSegment_087_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 394 15 16, g32p_row07_traceSegment_087_0394_0015, g32p_row07_traceSegment_087_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 364 30 31, g32p_row07_traceSegment_087_0364_0030, g32p_row07_traceSegment_087_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 425 15 15, g32p_row07_traceSegment_087_0425_0015, g32p_row07_traceSegment_087_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 455 15 16, g32p_row07_traceSegment_087_0455_0015, g32p_row07_traceSegment_087_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 425 30 31, g32p_row07_traceSegment_087_0425_0030, g32p_row07_traceSegment_087_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_087 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 364 61 61, g32p_row07_traceSegment_087_0364_0061, g32p_row07_traceSegment_087_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_087 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 243 121 122, g32p_row07_traceSegment_087_0243_0121, g32p_row07_traceSegment_087_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_087 0 486 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 0 243 243, g32p_row07_traceSegment_087_0000_0243, g32p_row07_traceSegment_087_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 486 15 15, g32p_row07_traceSegment_087_0486_0015, g32p_row07_traceSegment_087_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 516 15 15, g32p_row07_traceSegment_087_0516_0015, g32p_row07_traceSegment_087_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_087 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 486 30 30, g32p_row07_traceSegment_087_0486_0030, g32p_row07_traceSegment_087_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 546 15 15, g32p_row07_traceSegment_087_0546_0015, g32p_row07_traceSegment_087_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 576 15 16, g32p_row07_traceSegment_087_0576_0015, g32p_row07_traceSegment_087_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 546 30 31, g32p_row07_traceSegment_087_0546_0030, g32p_row07_traceSegment_087_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_087 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 486 60 61, g32p_row07_traceSegment_087_0486_0060, g32p_row07_traceSegment_087_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 607 15 15, g32p_row07_traceSegment_087_0607_0015, g32p_row07_traceSegment_087_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 637 15 16, g32p_row07_traceSegment_087_0637_0015, g32p_row07_traceSegment_087_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 607 30 31, g32p_row07_traceSegment_087_0607_0030, g32p_row07_traceSegment_087_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 668 15 15, g32p_row07_traceSegment_087_0668_0015, g32p_row07_traceSegment_087_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 698 15 16, g32p_row07_traceSegment_087_0698_0015, g32p_row07_traceSegment_087_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 668 30 31, g32p_row07_traceSegment_087_0668_0030, g32p_row07_traceSegment_087_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_087 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 607 61 61, g32p_row07_traceSegment_087_0607_0061, g32p_row07_traceSegment_087_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_087 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 486 121 122, g32p_row07_traceSegment_087_0486_0121, g32p_row07_traceSegment_087_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 729 15 15, g32p_row07_traceSegment_087_0729_0015, g32p_row07_traceSegment_087_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 759 15 15, g32p_row07_traceSegment_087_0759_0015, g32p_row07_traceSegment_087_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_087 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 729 30 30, g32p_row07_traceSegment_087_0729_0030, g32p_row07_traceSegment_087_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 789 15 15, g32p_row07_traceSegment_087_0789_0015, g32p_row07_traceSegment_087_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 819 15 16, g32p_row07_traceSegment_087_0819_0015, g32p_row07_traceSegment_087_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 789 30 31, g32p_row07_traceSegment_087_0789_0030, g32p_row07_traceSegment_087_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_087 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 729 60 61, g32p_row07_traceSegment_087_0729_0060, g32p_row07_traceSegment_087_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 850 15 15, g32p_row07_traceSegment_087_0850_0015, g32p_row07_traceSegment_087_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 880 15 16, g32p_row07_traceSegment_087_0880_0015, g32p_row07_traceSegment_087_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 850 30 31, g32p_row07_traceSegment_087_0850_0030, g32p_row07_traceSegment_087_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 911 15 15, g32p_row07_traceSegment_087_0911_0015, g32p_row07_traceSegment_087_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 941 15 16, g32p_row07_traceSegment_087_0941_0015, g32p_row07_traceSegment_087_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 911 30 31, g32p_row07_traceSegment_087_0911_0030, g32p_row07_traceSegment_087_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_087 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 850 61 61, g32p_row07_traceSegment_087_0850_0061, g32p_row07_traceSegment_087_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_087 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 729 121 122, g32p_row07_traceSegment_087_0729_0121, g32p_row07_traceSegment_087_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_087 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 486 243 243, g32p_row07_traceSegment_087_0486_0243, g32p_row07_traceSegment_087_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_087 0 972 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 0 486 486, g32p_row07_traceSegment_087_0000_0486, g32p_row07_traceSegment_087_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 972 15 15, g32p_row07_traceSegment_087_0972_0015, g32p_row07_traceSegment_087_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1002 15 15, g32p_row07_traceSegment_087_1002_0015, g32p_row07_traceSegment_087_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_087 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 972 30 30, g32p_row07_traceSegment_087_0972_0030, g32p_row07_traceSegment_087_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1032 15 15, g32p_row07_traceSegment_087_1032_0015, g32p_row07_traceSegment_087_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1062 15 16, g32p_row07_traceSegment_087_1062_0015, g32p_row07_traceSegment_087_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1032 30 31, g32p_row07_traceSegment_087_1032_0030, g32p_row07_traceSegment_087_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_087 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 972 60 61, g32p_row07_traceSegment_087_0972_0060, g32p_row07_traceSegment_087_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1093 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1093 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1093 15 15, g32p_row07_traceSegment_087_1093_0015, g32p_row07_traceSegment_087_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1123 15 16, g32p_row07_traceSegment_087_1123_0015, g32p_row07_traceSegment_087_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1093 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1093 30 31, g32p_row07_traceSegment_087_1093_0030, g32p_row07_traceSegment_087_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1154 15 15, g32p_row07_traceSegment_087_1154_0015, g32p_row07_traceSegment_087_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1184 15 16, g32p_row07_traceSegment_087_1184_0015, g32p_row07_traceSegment_087_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1154 30 31, g32p_row07_traceSegment_087_1154_0030, g32p_row07_traceSegment_087_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_087 1093 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1093 61 61, g32p_row07_traceSegment_087_1093_0061, g32p_row07_traceSegment_087_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_087 972 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 972 121 122, g32p_row07_traceSegment_087_0972_0121, g32p_row07_traceSegment_087_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1215 15 15, g32p_row07_traceSegment_087_1215_0015, g32p_row07_traceSegment_087_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1245 15 15, g32p_row07_traceSegment_087_1245_0015, g32p_row07_traceSegment_087_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_087 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1215 30 30, g32p_row07_traceSegment_087_1215_0030, g32p_row07_traceSegment_087_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1275 15 15, g32p_row07_traceSegment_087_1275_0015, g32p_row07_traceSegment_087_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1305 15 16, g32p_row07_traceSegment_087_1305_0015, g32p_row07_traceSegment_087_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1275 30 31, g32p_row07_traceSegment_087_1275_0030, g32p_row07_traceSegment_087_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_087 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1215 60 61, g32p_row07_traceSegment_087_1215_0060, g32p_row07_traceSegment_087_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1336 15 15, g32p_row07_traceSegment_087_1336_0015, g32p_row07_traceSegment_087_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1366 15 16, g32p_row07_traceSegment_087_1366_0015, g32p_row07_traceSegment_087_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1336 30 31, g32p_row07_traceSegment_087_1336_0030, g32p_row07_traceSegment_087_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1397 15 15, g32p_row07_traceSegment_087_1397_0015, g32p_row07_traceSegment_087_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1427 15 16, g32p_row07_traceSegment_087_1427_0015, g32p_row07_traceSegment_087_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1397 30 31, g32p_row07_traceSegment_087_1397_0030, g32p_row07_traceSegment_087_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_087 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1336 61 61, g32p_row07_traceSegment_087_1336_0061, g32p_row07_traceSegment_087_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_087 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1215 121 122, g32p_row07_traceSegment_087_1215_0121, g32p_row07_traceSegment_087_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_087 972 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 972 243 243, g32p_row07_traceSegment_087_0972_0243, g32p_row07_traceSegment_087_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1458 15 15, g32p_row07_traceSegment_087_1458_0015, g32p_row07_traceSegment_087_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1488 15 15, g32p_row07_traceSegment_087_1488_0015, g32p_row07_traceSegment_087_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_087 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1458 30 30, g32p_row07_traceSegment_087_1458_0030, g32p_row07_traceSegment_087_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1518 15 15, g32p_row07_traceSegment_087_1518_0015, g32p_row07_traceSegment_087_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1548 15 16, g32p_row07_traceSegment_087_1548_0015, g32p_row07_traceSegment_087_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1518 30 31, g32p_row07_traceSegment_087_1518_0030, g32p_row07_traceSegment_087_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_087 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1458 60 61, g32p_row07_traceSegment_087_1458_0060, g32p_row07_traceSegment_087_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1579 15 15, g32p_row07_traceSegment_087_1579_0015, g32p_row07_traceSegment_087_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1609 15 16, g32p_row07_traceSegment_087_1609_0015, g32p_row07_traceSegment_087_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1579 30 31, g32p_row07_traceSegment_087_1579_0030, g32p_row07_traceSegment_087_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1640 15 15, g32p_row07_traceSegment_087_1640_0015, g32p_row07_traceSegment_087_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1670 15 16, g32p_row07_traceSegment_087_1670_0015, g32p_row07_traceSegment_087_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1640 30 31, g32p_row07_traceSegment_087_1640_0030, g32p_row07_traceSegment_087_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_087 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1579 61 61, g32p_row07_traceSegment_087_1579_0061, g32p_row07_traceSegment_087_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_087 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1458 121 122, g32p_row07_traceSegment_087_1458_0121, g32p_row07_traceSegment_087_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1701 15 15, g32p_row07_traceSegment_087_1701_0015, g32p_row07_traceSegment_087_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1731 15 15, g32p_row07_traceSegment_087_1731_0015, g32p_row07_traceSegment_087_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_087 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1701 30 30, g32p_row07_traceSegment_087_1701_0030, g32p_row07_traceSegment_087_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1761 15 15, g32p_row07_traceSegment_087_1761_0015, g32p_row07_traceSegment_087_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1791 15 16, g32p_row07_traceSegment_087_1791_0015, g32p_row07_traceSegment_087_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1761 30 31, g32p_row07_traceSegment_087_1761_0030, g32p_row07_traceSegment_087_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_087 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1701 60 61, g32p_row07_traceSegment_087_1701_0060, g32p_row07_traceSegment_087_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1822 15 15, g32p_row07_traceSegment_087_1822_0015, g32p_row07_traceSegment_087_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1852 15 16, g32p_row07_traceSegment_087_1852_0015, g32p_row07_traceSegment_087_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1822 30 31, g32p_row07_traceSegment_087_1822_0030, g32p_row07_traceSegment_087_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_087 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1883 15 15, g32p_row07_traceSegment_087_1883_0015, g32p_row07_traceSegment_087_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_087 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_087 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_087_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_087 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1913 15 16, g32p_row07_traceSegment_087_1913_0015, g32p_row07_traceSegment_087_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_087 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1883 30 31, g32p_row07_traceSegment_087_1883_0030, g32p_row07_traceSegment_087_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_087 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1822 61 61, g32p_row07_traceSegment_087_1822_0061, g32p_row07_traceSegment_087_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_087 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1701 121 122, g32p_row07_traceSegment_087_1701_0121, g32p_row07_traceSegment_087_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_087_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_087 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 1458 243 243, g32p_row07_traceSegment_087_1458_0243, g32p_row07_traceSegment_087_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_087 972 972 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 972 486 486, g32p_row07_traceSegment_087_0972_0486, g32p_row07_traceSegment_087_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_087_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_087 0 1944 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_087 0 972 972, g32p_row07_traceSegment_087_0000_0972, g32p_row07_traceSegment_087_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 87 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_087_0000_1944

end HodgeLean.Foundations.Program

end
end
