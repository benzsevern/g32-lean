import HodgeLean.Foundations.Program.G32PropFourSixPacked0347
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0351

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_088 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 88 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_088_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 0 15 15, g32p_row07_traceSegment_088_0000_0015, g32p_row07_traceSegment_088_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 30 15 15, g32p_row07_traceSegment_088_0030_0015, g32p_row07_traceSegment_088_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_088 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 0 30 30, g32p_row07_traceSegment_088_0000_0030, g32p_row07_traceSegment_088_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 60 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 75 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 60 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 60 15 15, g32p_row07_traceSegment_088_0060_0015, g32p_row07_traceSegment_088_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 90 15 16, g32p_row07_traceSegment_088_0090_0015, g32p_row07_traceSegment_088_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 60 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 60 30 31, g32p_row07_traceSegment_088_0060_0030, g32p_row07_traceSegment_088_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_088 0 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 0 60 61, g32p_row07_traceSegment_088_0000_0060, g32p_row07_traceSegment_088_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 121 15 15, g32p_row07_traceSegment_088_0121_0015, g32p_row07_traceSegment_088_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 151 15 16, g32p_row07_traceSegment_088_0151_0015, g32p_row07_traceSegment_088_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 121 30 31, g32p_row07_traceSegment_088_0121_0030, g32p_row07_traceSegment_088_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 182 15 15, g32p_row07_traceSegment_088_0182_0015, g32p_row07_traceSegment_088_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 212 15 16, g32p_row07_traceSegment_088_0212_0015, g32p_row07_traceSegment_088_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 182 30 31, g32p_row07_traceSegment_088_0182_0030, g32p_row07_traceSegment_088_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_088 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 121 61 61, g32p_row07_traceSegment_088_0121_0061, g32p_row07_traceSegment_088_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_088 0 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 0 121 122, g32p_row07_traceSegment_088_0000_0121, g32p_row07_traceSegment_088_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 243 15 15, g32p_row07_traceSegment_088_0243_0015, g32p_row07_traceSegment_088_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 273 15 15, g32p_row07_traceSegment_088_0273_0015, g32p_row07_traceSegment_088_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_088 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 243 30 30, g32p_row07_traceSegment_088_0243_0030, g32p_row07_traceSegment_088_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 303 15 15, g32p_row07_traceSegment_088_0303_0015, g32p_row07_traceSegment_088_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 333 15 16, g32p_row07_traceSegment_088_0333_0015, g32p_row07_traceSegment_088_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 303 30 31, g32p_row07_traceSegment_088_0303_0030, g32p_row07_traceSegment_088_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_088 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 243 60 61, g32p_row07_traceSegment_088_0243_0060, g32p_row07_traceSegment_088_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 364 15 15, g32p_row07_traceSegment_088_0364_0015, g32p_row07_traceSegment_088_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 394 15 16, g32p_row07_traceSegment_088_0394_0015, g32p_row07_traceSegment_088_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 364 30 31, g32p_row07_traceSegment_088_0364_0030, g32p_row07_traceSegment_088_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 425 15 15, g32p_row07_traceSegment_088_0425_0015, g32p_row07_traceSegment_088_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 455 15 16, g32p_row07_traceSegment_088_0455_0015, g32p_row07_traceSegment_088_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 425 30 31, g32p_row07_traceSegment_088_0425_0030, g32p_row07_traceSegment_088_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_088 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 364 61 61, g32p_row07_traceSegment_088_0364_0061, g32p_row07_traceSegment_088_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_088 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 243 121 122, g32p_row07_traceSegment_088_0243_0121, g32p_row07_traceSegment_088_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_088 0 486 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 0 243 243, g32p_row07_traceSegment_088_0000_0243, g32p_row07_traceSegment_088_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 486 15 15, g32p_row07_traceSegment_088_0486_0015, g32p_row07_traceSegment_088_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 516 15 15, g32p_row07_traceSegment_088_0516_0015, g32p_row07_traceSegment_088_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_088 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 486 30 30, g32p_row07_traceSegment_088_0486_0030, g32p_row07_traceSegment_088_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 546 15 15, g32p_row07_traceSegment_088_0546_0015, g32p_row07_traceSegment_088_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 576 15 16, g32p_row07_traceSegment_088_0576_0015, g32p_row07_traceSegment_088_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 546 30 31, g32p_row07_traceSegment_088_0546_0030, g32p_row07_traceSegment_088_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_088 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 486 60 61, g32p_row07_traceSegment_088_0486_0060, g32p_row07_traceSegment_088_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 607 15 15, g32p_row07_traceSegment_088_0607_0015, g32p_row07_traceSegment_088_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 637 15 16, g32p_row07_traceSegment_088_0637_0015, g32p_row07_traceSegment_088_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 607 30 31, g32p_row07_traceSegment_088_0607_0030, g32p_row07_traceSegment_088_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 668 15 15, g32p_row07_traceSegment_088_0668_0015, g32p_row07_traceSegment_088_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 698 15 16, g32p_row07_traceSegment_088_0698_0015, g32p_row07_traceSegment_088_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 668 30 31, g32p_row07_traceSegment_088_0668_0030, g32p_row07_traceSegment_088_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_088 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 607 61 61, g32p_row07_traceSegment_088_0607_0061, g32p_row07_traceSegment_088_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_088 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 486 121 122, g32p_row07_traceSegment_088_0486_0121, g32p_row07_traceSegment_088_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 729 15 15, g32p_row07_traceSegment_088_0729_0015, g32p_row07_traceSegment_088_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 774 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 759 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 759 15 15, g32p_row07_traceSegment_088_0759_0015, g32p_row07_traceSegment_088_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_088 729 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 729 30 30, g32p_row07_traceSegment_088_0729_0030, g32p_row07_traceSegment_088_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 789 15 15, g32p_row07_traceSegment_088_0789_0015, g32p_row07_traceSegment_088_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 819 15 16, g32p_row07_traceSegment_088_0819_0015, g32p_row07_traceSegment_088_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 789 30 31, g32p_row07_traceSegment_088_0789_0030, g32p_row07_traceSegment_088_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_088 729 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 729 60 61, g32p_row07_traceSegment_088_0729_0060, g32p_row07_traceSegment_088_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 850 15 15, g32p_row07_traceSegment_088_0850_0015, g32p_row07_traceSegment_088_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 880 15 16, g32p_row07_traceSegment_088_0880_0015, g32p_row07_traceSegment_088_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 850 30 31, g32p_row07_traceSegment_088_0850_0030, g32p_row07_traceSegment_088_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 911 15 15, g32p_row07_traceSegment_088_0911_0015, g32p_row07_traceSegment_088_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 941 15 16, g32p_row07_traceSegment_088_0941_0015, g32p_row07_traceSegment_088_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 911 30 31, g32p_row07_traceSegment_088_0911_0030, g32p_row07_traceSegment_088_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_088 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 850 61 61, g32p_row07_traceSegment_088_0850_0061, g32p_row07_traceSegment_088_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_088 729 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 729 121 122, g32p_row07_traceSegment_088_0729_0121, g32p_row07_traceSegment_088_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_088 486 486 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 486 243 243, g32p_row07_traceSegment_088_0486_0243, g32p_row07_traceSegment_088_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_088 0 972 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 0 486 486, g32p_row07_traceSegment_088_0000_0486, g32p_row07_traceSegment_088_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 972 15 15, g32p_row07_traceSegment_088_0972_0015, g32p_row07_traceSegment_088_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1002 15 15, g32p_row07_traceSegment_088_1002_0015, g32p_row07_traceSegment_088_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_088 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 972 30 30, g32p_row07_traceSegment_088_0972_0030, g32p_row07_traceSegment_088_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1032 15 15, g32p_row07_traceSegment_088_1032_0015, g32p_row07_traceSegment_088_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1062 15 16, g32p_row07_traceSegment_088_1062_0015, g32p_row07_traceSegment_088_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1032 30 31, g32p_row07_traceSegment_088_1032_0030, g32p_row07_traceSegment_088_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_088 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 972 60 61, g32p_row07_traceSegment_088_0972_0060, g32p_row07_traceSegment_088_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1093 15 15, g32p_row07_traceSegment_088_1093_0015, g32p_row07_traceSegment_088_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1123 15 16, g32p_row07_traceSegment_088_1123_0015, g32p_row07_traceSegment_088_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1093 30 31, g32p_row07_traceSegment_088_1093_0030, g32p_row07_traceSegment_088_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1154 15 15, g32p_row07_traceSegment_088_1154_0015, g32p_row07_traceSegment_088_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1184 15 16, g32p_row07_traceSegment_088_1184_0015, g32p_row07_traceSegment_088_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1154 30 31, g32p_row07_traceSegment_088_1154_0030, g32p_row07_traceSegment_088_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_088 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1093 61 61, g32p_row07_traceSegment_088_1093_0061, g32p_row07_traceSegment_088_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_088 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 972 121 122, g32p_row07_traceSegment_088_0972_0121, g32p_row07_traceSegment_088_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1215 15 15, g32p_row07_traceSegment_088_1215_0015, g32p_row07_traceSegment_088_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1245 15 15, g32p_row07_traceSegment_088_1245_0015, g32p_row07_traceSegment_088_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_088 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1215 30 30, g32p_row07_traceSegment_088_1215_0030, g32p_row07_traceSegment_088_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1275 15 15, g32p_row07_traceSegment_088_1275_0015, g32p_row07_traceSegment_088_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1305 15 16, g32p_row07_traceSegment_088_1305_0015, g32p_row07_traceSegment_088_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1275 30 31, g32p_row07_traceSegment_088_1275_0030, g32p_row07_traceSegment_088_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_088 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1215 60 61, g32p_row07_traceSegment_088_1215_0060, g32p_row07_traceSegment_088_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1336 15 15, g32p_row07_traceSegment_088_1336_0015, g32p_row07_traceSegment_088_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1366 15 16, g32p_row07_traceSegment_088_1366_0015, g32p_row07_traceSegment_088_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1336 30 31, g32p_row07_traceSegment_088_1336_0030, g32p_row07_traceSegment_088_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1397 15 15, g32p_row07_traceSegment_088_1397_0015, g32p_row07_traceSegment_088_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1427 15 16, g32p_row07_traceSegment_088_1427_0015, g32p_row07_traceSegment_088_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1397 30 31, g32p_row07_traceSegment_088_1397_0030, g32p_row07_traceSegment_088_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_088 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1336 61 61, g32p_row07_traceSegment_088_1336_0061, g32p_row07_traceSegment_088_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_088 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1215 121 122, g32p_row07_traceSegment_088_1215_0121, g32p_row07_traceSegment_088_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_088 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 972 243 243, g32p_row07_traceSegment_088_0972_0243, g32p_row07_traceSegment_088_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1458 15 15, g32p_row07_traceSegment_088_1458_0015, g32p_row07_traceSegment_088_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1488 15 15, g32p_row07_traceSegment_088_1488_0015, g32p_row07_traceSegment_088_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_088 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1458 30 30, g32p_row07_traceSegment_088_1458_0030, g32p_row07_traceSegment_088_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1518 15 15, g32p_row07_traceSegment_088_1518_0015, g32p_row07_traceSegment_088_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1548 15 16, g32p_row07_traceSegment_088_1548_0015, g32p_row07_traceSegment_088_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1518 30 31, g32p_row07_traceSegment_088_1518_0030, g32p_row07_traceSegment_088_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_088 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1458 60 61, g32p_row07_traceSegment_088_1458_0060, g32p_row07_traceSegment_088_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1579 15 15, g32p_row07_traceSegment_088_1579_0015, g32p_row07_traceSegment_088_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1609 15 16, g32p_row07_traceSegment_088_1609_0015, g32p_row07_traceSegment_088_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1579 30 31, g32p_row07_traceSegment_088_1579_0030, g32p_row07_traceSegment_088_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1640 15 15, g32p_row07_traceSegment_088_1640_0015, g32p_row07_traceSegment_088_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1670 15 16, g32p_row07_traceSegment_088_1670_0015, g32p_row07_traceSegment_088_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1640 30 31, g32p_row07_traceSegment_088_1640_0030, g32p_row07_traceSegment_088_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_088 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1579 61 61, g32p_row07_traceSegment_088_1579_0061, g32p_row07_traceSegment_088_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_088 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1458 121 122, g32p_row07_traceSegment_088_1458_0121, g32p_row07_traceSegment_088_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1701 15 15, g32p_row07_traceSegment_088_1701_0015, g32p_row07_traceSegment_088_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1731 15 15, g32p_row07_traceSegment_088_1731_0015, g32p_row07_traceSegment_088_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_088 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1701 30 30, g32p_row07_traceSegment_088_1701_0030, g32p_row07_traceSegment_088_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1761 15 15, g32p_row07_traceSegment_088_1761_0015, g32p_row07_traceSegment_088_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1791 15 16, g32p_row07_traceSegment_088_1791_0015, g32p_row07_traceSegment_088_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1761 30 31, g32p_row07_traceSegment_088_1761_0030, g32p_row07_traceSegment_088_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_088 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1701 60 61, g32p_row07_traceSegment_088_1701_0060, g32p_row07_traceSegment_088_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1822 15 15, g32p_row07_traceSegment_088_1822_0015, g32p_row07_traceSegment_088_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1852 15 16, g32p_row07_traceSegment_088_1852_0015, g32p_row07_traceSegment_088_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1822 30 31, g32p_row07_traceSegment_088_1822_0030, g32p_row07_traceSegment_088_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_088 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1883 15 15, g32p_row07_traceSegment_088_1883_0015, g32p_row07_traceSegment_088_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_088 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_088 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_088_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_088 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1913 15 16, g32p_row07_traceSegment_088_1913_0015, g32p_row07_traceSegment_088_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_088 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1883 30 31, g32p_row07_traceSegment_088_1883_0030, g32p_row07_traceSegment_088_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_088 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1822 61 61, g32p_row07_traceSegment_088_1822_0061, g32p_row07_traceSegment_088_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_088 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1701 121 122, g32p_row07_traceSegment_088_1701_0121, g32p_row07_traceSegment_088_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_088_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_088 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 1458 243 243, g32p_row07_traceSegment_088_1458_0243, g32p_row07_traceSegment_088_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_088 972 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 972 486 486, g32p_row07_traceSegment_088_0972_0486, g32p_row07_traceSegment_088_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_088_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_088 0 1944 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_088 0 972 972, g32p_row07_traceSegment_088_0000_0972, g32p_row07_traceSegment_088_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 88 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_088_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_092 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 92 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_092_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 0 15 15, g32p_row07_traceSegment_092_0000_0015, g32p_row07_traceSegment_092_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 30 15 15, g32p_row07_traceSegment_092_0030_0015, g32p_row07_traceSegment_092_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_092 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 0 30 30, g32p_row07_traceSegment_092_0000_0030, g32p_row07_traceSegment_092_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 60 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 60 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 60 15 15, g32p_row07_traceSegment_092_0060_0015, g32p_row07_traceSegment_092_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 90 15 16, g32p_row07_traceSegment_092_0090_0015, g32p_row07_traceSegment_092_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 60 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 60 30 31, g32p_row07_traceSegment_092_0060_0030, g32p_row07_traceSegment_092_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_092 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 0 60 61, g32p_row07_traceSegment_092_0000_0060, g32p_row07_traceSegment_092_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 121 15 15, g32p_row07_traceSegment_092_0121_0015, g32p_row07_traceSegment_092_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 151 15 16, g32p_row07_traceSegment_092_0151_0015, g32p_row07_traceSegment_092_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 121 30 31, g32p_row07_traceSegment_092_0121_0030, g32p_row07_traceSegment_092_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 182 15 15, g32p_row07_traceSegment_092_0182_0015, g32p_row07_traceSegment_092_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 212 15 16, g32p_row07_traceSegment_092_0212_0015, g32p_row07_traceSegment_092_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 182 30 31, g32p_row07_traceSegment_092_0182_0030, g32p_row07_traceSegment_092_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_092 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 121 61 61, g32p_row07_traceSegment_092_0121_0061, g32p_row07_traceSegment_092_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_092 0 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 0 121 122, g32p_row07_traceSegment_092_0000_0121, g32p_row07_traceSegment_092_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 243 15 15, g32p_row07_traceSegment_092_0243_0015, g32p_row07_traceSegment_092_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 273 15 15, g32p_row07_traceSegment_092_0273_0015, g32p_row07_traceSegment_092_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_092 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 243 30 30, g32p_row07_traceSegment_092_0243_0030, g32p_row07_traceSegment_092_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 303 15 15, g32p_row07_traceSegment_092_0303_0015, g32p_row07_traceSegment_092_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 333 15 16, g32p_row07_traceSegment_092_0333_0015, g32p_row07_traceSegment_092_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 303 30 31, g32p_row07_traceSegment_092_0303_0030, g32p_row07_traceSegment_092_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_092 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 243 60 61, g32p_row07_traceSegment_092_0243_0060, g32p_row07_traceSegment_092_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 364 15 15, g32p_row07_traceSegment_092_0364_0015, g32p_row07_traceSegment_092_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 394 15 16, g32p_row07_traceSegment_092_0394_0015, g32p_row07_traceSegment_092_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 364 30 31, g32p_row07_traceSegment_092_0364_0030, g32p_row07_traceSegment_092_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 425 15 15, g32p_row07_traceSegment_092_0425_0015, g32p_row07_traceSegment_092_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 455 15 16, g32p_row07_traceSegment_092_0455_0015, g32p_row07_traceSegment_092_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 425 30 31, g32p_row07_traceSegment_092_0425_0030, g32p_row07_traceSegment_092_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_092 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 364 61 61, g32p_row07_traceSegment_092_0364_0061, g32p_row07_traceSegment_092_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_092 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 243 121 122, g32p_row07_traceSegment_092_0243_0121, g32p_row07_traceSegment_092_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_092 0 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 0 243 243, g32p_row07_traceSegment_092_0000_0243, g32p_row07_traceSegment_092_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 486 15 15, g32p_row07_traceSegment_092_0486_0015, g32p_row07_traceSegment_092_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 516 15 15, g32p_row07_traceSegment_092_0516_0015, g32p_row07_traceSegment_092_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_092 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 486 30 30, g32p_row07_traceSegment_092_0486_0030, g32p_row07_traceSegment_092_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 546 15 15, g32p_row07_traceSegment_092_0546_0015, g32p_row07_traceSegment_092_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 576 15 16, g32p_row07_traceSegment_092_0576_0015, g32p_row07_traceSegment_092_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 546 30 31, g32p_row07_traceSegment_092_0546_0030, g32p_row07_traceSegment_092_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_092 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 486 60 61, g32p_row07_traceSegment_092_0486_0060, g32p_row07_traceSegment_092_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 607 15 15, g32p_row07_traceSegment_092_0607_0015, g32p_row07_traceSegment_092_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 637 15 16, g32p_row07_traceSegment_092_0637_0015, g32p_row07_traceSegment_092_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 607 30 31, g32p_row07_traceSegment_092_0607_0030, g32p_row07_traceSegment_092_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 668 15 15, g32p_row07_traceSegment_092_0668_0015, g32p_row07_traceSegment_092_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 698 15 16, g32p_row07_traceSegment_092_0698_0015, g32p_row07_traceSegment_092_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 668 30 31, g32p_row07_traceSegment_092_0668_0030, g32p_row07_traceSegment_092_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_092 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 607 61 61, g32p_row07_traceSegment_092_0607_0061, g32p_row07_traceSegment_092_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_092 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 486 121 122, g32p_row07_traceSegment_092_0486_0121, g32p_row07_traceSegment_092_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 729 15 15, g32p_row07_traceSegment_092_0729_0015, g32p_row07_traceSegment_092_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 759 15 15, g32p_row07_traceSegment_092_0759_0015, g32p_row07_traceSegment_092_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_092 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 729 30 30, g32p_row07_traceSegment_092_0729_0030, g32p_row07_traceSegment_092_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 789 15 15, g32p_row07_traceSegment_092_0789_0015, g32p_row07_traceSegment_092_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 819 15 16, g32p_row07_traceSegment_092_0819_0015, g32p_row07_traceSegment_092_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 789 30 31, g32p_row07_traceSegment_092_0789_0030, g32p_row07_traceSegment_092_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_092 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 729 60 61, g32p_row07_traceSegment_092_0729_0060, g32p_row07_traceSegment_092_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 850 15 15, g32p_row07_traceSegment_092_0850_0015, g32p_row07_traceSegment_092_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 880 15 16, g32p_row07_traceSegment_092_0880_0015, g32p_row07_traceSegment_092_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 850 30 31, g32p_row07_traceSegment_092_0850_0030, g32p_row07_traceSegment_092_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 926 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 911 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 911 15 15, g32p_row07_traceSegment_092_0911_0015, g32p_row07_traceSegment_092_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 941 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 941 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 941 15 16, g32p_row07_traceSegment_092_0941_0015, g32p_row07_traceSegment_092_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 911 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 911 30 31, g32p_row07_traceSegment_092_0911_0030, g32p_row07_traceSegment_092_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_092 850 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 850 61 61, g32p_row07_traceSegment_092_0850_0061, g32p_row07_traceSegment_092_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_092 729 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 729 121 122, g32p_row07_traceSegment_092_0729_0121, g32p_row07_traceSegment_092_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_092 486 486 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 486 243 243, g32p_row07_traceSegment_092_0486_0243, g32p_row07_traceSegment_092_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_092 0 972 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 0 486 486, g32p_row07_traceSegment_092_0000_0486, g32p_row07_traceSegment_092_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 972 15 15, g32p_row07_traceSegment_092_0972_0015, g32p_row07_traceSegment_092_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1002 15 15, g32p_row07_traceSegment_092_1002_0015, g32p_row07_traceSegment_092_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_092 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 972 30 30, g32p_row07_traceSegment_092_0972_0030, g32p_row07_traceSegment_092_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1032 15 15, g32p_row07_traceSegment_092_1032_0015, g32p_row07_traceSegment_092_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1077 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1062 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1062 15 16, g32p_row07_traceSegment_092_1062_0015, g32p_row07_traceSegment_092_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1032 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1032 30 31, g32p_row07_traceSegment_092_1032_0030, g32p_row07_traceSegment_092_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_092 972 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 972 60 61, g32p_row07_traceSegment_092_0972_0060, g32p_row07_traceSegment_092_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1108 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1093 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1093 15 15, g32p_row07_traceSegment_092_1093_0015, g32p_row07_traceSegment_092_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1123 15 16, g32p_row07_traceSegment_092_1123_0015, g32p_row07_traceSegment_092_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1093 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1093 30 31, g32p_row07_traceSegment_092_1093_0030, g32p_row07_traceSegment_092_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1154 15 15, g32p_row07_traceSegment_092_1154_0015, g32p_row07_traceSegment_092_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1184 15 16, g32p_row07_traceSegment_092_1184_0015, g32p_row07_traceSegment_092_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1154 30 31, g32p_row07_traceSegment_092_1154_0030, g32p_row07_traceSegment_092_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_092 1093 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1093 61 61, g32p_row07_traceSegment_092_1093_0061, g32p_row07_traceSegment_092_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_092 972 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 972 121 122, g32p_row07_traceSegment_092_0972_0121, g32p_row07_traceSegment_092_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1215 15 15, g32p_row07_traceSegment_092_1215_0015, g32p_row07_traceSegment_092_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1245 15 15, g32p_row07_traceSegment_092_1245_0015, g32p_row07_traceSegment_092_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_092 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1215 30 30, g32p_row07_traceSegment_092_1215_0030, g32p_row07_traceSegment_092_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1275 15 15, g32p_row07_traceSegment_092_1275_0015, g32p_row07_traceSegment_092_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1305 15 16, g32p_row07_traceSegment_092_1305_0015, g32p_row07_traceSegment_092_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1275 30 31, g32p_row07_traceSegment_092_1275_0030, g32p_row07_traceSegment_092_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_092 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1215 60 61, g32p_row07_traceSegment_092_1215_0060, g32p_row07_traceSegment_092_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1336 15 15, g32p_row07_traceSegment_092_1336_0015, g32p_row07_traceSegment_092_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1366 15 16, g32p_row07_traceSegment_092_1366_0015, g32p_row07_traceSegment_092_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1336 30 31, g32p_row07_traceSegment_092_1336_0030, g32p_row07_traceSegment_092_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1397 15 15, g32p_row07_traceSegment_092_1397_0015, g32p_row07_traceSegment_092_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1427 15 16, g32p_row07_traceSegment_092_1427_0015, g32p_row07_traceSegment_092_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1397 30 31, g32p_row07_traceSegment_092_1397_0030, g32p_row07_traceSegment_092_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_092 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1336 61 61, g32p_row07_traceSegment_092_1336_0061, g32p_row07_traceSegment_092_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_092 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1215 121 122, g32p_row07_traceSegment_092_1215_0121, g32p_row07_traceSegment_092_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_092 972 486 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 972 243 243, g32p_row07_traceSegment_092_0972_0243, g32p_row07_traceSegment_092_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1458 15 15, g32p_row07_traceSegment_092_1458_0015, g32p_row07_traceSegment_092_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1488 15 15, g32p_row07_traceSegment_092_1488_0015, g32p_row07_traceSegment_092_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_092 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1458 30 30, g32p_row07_traceSegment_092_1458_0030, g32p_row07_traceSegment_092_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1518 15 15, g32p_row07_traceSegment_092_1518_0015, g32p_row07_traceSegment_092_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1548 15 16, g32p_row07_traceSegment_092_1548_0015, g32p_row07_traceSegment_092_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1518 30 31, g32p_row07_traceSegment_092_1518_0030, g32p_row07_traceSegment_092_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_092 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1458 60 61, g32p_row07_traceSegment_092_1458_0060, g32p_row07_traceSegment_092_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1579 15 15, g32p_row07_traceSegment_092_1579_0015, g32p_row07_traceSegment_092_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1609 15 16, g32p_row07_traceSegment_092_1609_0015, g32p_row07_traceSegment_092_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1579 30 31, g32p_row07_traceSegment_092_1579_0030, g32p_row07_traceSegment_092_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1640 15 15, g32p_row07_traceSegment_092_1640_0015, g32p_row07_traceSegment_092_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1670 15 16, g32p_row07_traceSegment_092_1670_0015, g32p_row07_traceSegment_092_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1640 30 31, g32p_row07_traceSegment_092_1640_0030, g32p_row07_traceSegment_092_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_092 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1579 61 61, g32p_row07_traceSegment_092_1579_0061, g32p_row07_traceSegment_092_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_092 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1458 121 122, g32p_row07_traceSegment_092_1458_0121, g32p_row07_traceSegment_092_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1701 15 15, g32p_row07_traceSegment_092_1701_0015, g32p_row07_traceSegment_092_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1731 15 15, g32p_row07_traceSegment_092_1731_0015, g32p_row07_traceSegment_092_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_092 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1701 30 30, g32p_row07_traceSegment_092_1701_0030, g32p_row07_traceSegment_092_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1761 15 15, g32p_row07_traceSegment_092_1761_0015, g32p_row07_traceSegment_092_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1791 15 16, g32p_row07_traceSegment_092_1791_0015, g32p_row07_traceSegment_092_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1761 30 31, g32p_row07_traceSegment_092_1761_0030, g32p_row07_traceSegment_092_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_092 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1701 60 61, g32p_row07_traceSegment_092_1701_0060, g32p_row07_traceSegment_092_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1822 15 15, g32p_row07_traceSegment_092_1822_0015, g32p_row07_traceSegment_092_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1852 15 16, g32p_row07_traceSegment_092_1852_0015, g32p_row07_traceSegment_092_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1822 30 31, g32p_row07_traceSegment_092_1822_0030, g32p_row07_traceSegment_092_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_092 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1883 15 15, g32p_row07_traceSegment_092_1883_0015, g32p_row07_traceSegment_092_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_092 1913 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_092 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_092_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_092 1913 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1913 15 16, g32p_row07_traceSegment_092_1913_0015, g32p_row07_traceSegment_092_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_092 1883 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1883 30 31, g32p_row07_traceSegment_092_1883_0030, g32p_row07_traceSegment_092_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_092 1822 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1822 61 61, g32p_row07_traceSegment_092_1822_0061, g32p_row07_traceSegment_092_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_092 1701 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1701 121 122, g32p_row07_traceSegment_092_1701_0121, g32p_row07_traceSegment_092_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_092_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_092 1458 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 1458 243 243, g32p_row07_traceSegment_092_1458_0243, g32p_row07_traceSegment_092_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_092 972 972 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 972 486 486, g32p_row07_traceSegment_092_0972_0486, g32p_row07_traceSegment_092_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_092_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_092 0 1944 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_092 0 972 972, g32p_row07_traceSegment_092_0000_0972, g32p_row07_traceSegment_092_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 92 = [0, 0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_092_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row07_tracePolynomial_070 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 70) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 70) (g32p_literalTraceValue 6 70)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_070]
  decide +kernel

theorem g32p_row07_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 75) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 75) (g32p_literalTraceValue 6 75)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_075]
  decide +kernel

theorem g32p_row07_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 76) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 76) (g32p_literalTraceValue 6 76)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_076]
  decide +kernel

theorem g32p_row07_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 78) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 78) (g32p_literalTraceValue 6 78)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_078]
  decide +kernel

theorem g32p_row07_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 84) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 84) (g32p_literalTraceValue 6 84)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_084]
  decide +kernel

theorem g32p_row07_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 87) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 87) (g32p_literalTraceValue 6 87)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row07_traceCoefficients_087]
  decide +kernel

theorem g32p_row07_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 88) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 88) (g32p_literalTraceValue 6 88)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row07_traceCoefficients_088]
  decide +kernel

theorem g32p_row07_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 92) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 92) (g32p_literalTraceValue 6 92)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row07_traceCoefficients_092]
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

private def g32p_row07_traceSegment_093 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 93 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_093_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 0 15 15, g32p_row07_traceSegment_093_0000_0015, g32p_row07_traceSegment_093_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 30 15 15, g32p_row07_traceSegment_093_0030_0015, g32p_row07_traceSegment_093_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_093 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 0 30 30, g32p_row07_traceSegment_093_0000_0030, g32p_row07_traceSegment_093_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 60 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 75 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 60 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 60 15 15, g32p_row07_traceSegment_093_0060_0015, g32p_row07_traceSegment_093_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 90 15 16, g32p_row07_traceSegment_093_0090_0015, g32p_row07_traceSegment_093_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 60 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 60 30 31, g32p_row07_traceSegment_093_0060_0030, g32p_row07_traceSegment_093_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_093 0 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 0 60 61, g32p_row07_traceSegment_093_0000_0060, g32p_row07_traceSegment_093_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 121 15 15, g32p_row07_traceSegment_093_0121_0015, g32p_row07_traceSegment_093_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 151 15 16, g32p_row07_traceSegment_093_0151_0015, g32p_row07_traceSegment_093_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 121 30 31, g32p_row07_traceSegment_093_0121_0030, g32p_row07_traceSegment_093_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 182 15 15, g32p_row07_traceSegment_093_0182_0015, g32p_row07_traceSegment_093_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 212 15 16, g32p_row07_traceSegment_093_0212_0015, g32p_row07_traceSegment_093_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 182 30 31, g32p_row07_traceSegment_093_0182_0030, g32p_row07_traceSegment_093_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_093 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 121 61 61, g32p_row07_traceSegment_093_0121_0061, g32p_row07_traceSegment_093_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_093 0 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 0 121 122, g32p_row07_traceSegment_093_0000_0121, g32p_row07_traceSegment_093_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 243 15 15, g32p_row07_traceSegment_093_0243_0015, g32p_row07_traceSegment_093_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 273 15 15, g32p_row07_traceSegment_093_0273_0015, g32p_row07_traceSegment_093_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_093 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 243 30 30, g32p_row07_traceSegment_093_0243_0030, g32p_row07_traceSegment_093_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 303 15 15, g32p_row07_traceSegment_093_0303_0015, g32p_row07_traceSegment_093_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 333 15 16, g32p_row07_traceSegment_093_0333_0015, g32p_row07_traceSegment_093_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 303 30 31, g32p_row07_traceSegment_093_0303_0030, g32p_row07_traceSegment_093_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_093 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 243 60 61, g32p_row07_traceSegment_093_0243_0060, g32p_row07_traceSegment_093_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 364 15 15, g32p_row07_traceSegment_093_0364_0015, g32p_row07_traceSegment_093_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 394 15 16, g32p_row07_traceSegment_093_0394_0015, g32p_row07_traceSegment_093_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 364 30 31, g32p_row07_traceSegment_093_0364_0030, g32p_row07_traceSegment_093_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 425 15 15, g32p_row07_traceSegment_093_0425_0015, g32p_row07_traceSegment_093_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 455 15 16, g32p_row07_traceSegment_093_0455_0015, g32p_row07_traceSegment_093_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 425 30 31, g32p_row07_traceSegment_093_0425_0030, g32p_row07_traceSegment_093_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_093 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 364 61 61, g32p_row07_traceSegment_093_0364_0061, g32p_row07_traceSegment_093_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_093 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 243 121 122, g32p_row07_traceSegment_093_0243_0121, g32p_row07_traceSegment_093_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_093 0 486 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 0 243 243, g32p_row07_traceSegment_093_0000_0243, g32p_row07_traceSegment_093_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 486 15 15, g32p_row07_traceSegment_093_0486_0015, g32p_row07_traceSegment_093_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 516 15 15, g32p_row07_traceSegment_093_0516_0015, g32p_row07_traceSegment_093_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_093 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 486 30 30, g32p_row07_traceSegment_093_0486_0030, g32p_row07_traceSegment_093_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 546 15 15, g32p_row07_traceSegment_093_0546_0015, g32p_row07_traceSegment_093_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 576 15 16, g32p_row07_traceSegment_093_0576_0015, g32p_row07_traceSegment_093_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 546 30 31, g32p_row07_traceSegment_093_0546_0030, g32p_row07_traceSegment_093_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_093 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 486 60 61, g32p_row07_traceSegment_093_0486_0060, g32p_row07_traceSegment_093_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 607 15 15, g32p_row07_traceSegment_093_0607_0015, g32p_row07_traceSegment_093_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 637 15 16, g32p_row07_traceSegment_093_0637_0015, g32p_row07_traceSegment_093_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 607 30 31, g32p_row07_traceSegment_093_0607_0030, g32p_row07_traceSegment_093_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 668 15 15, g32p_row07_traceSegment_093_0668_0015, g32p_row07_traceSegment_093_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 698 15 16, g32p_row07_traceSegment_093_0698_0015, g32p_row07_traceSegment_093_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 668 30 31, g32p_row07_traceSegment_093_0668_0030, g32p_row07_traceSegment_093_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_093 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 607 61 61, g32p_row07_traceSegment_093_0607_0061, g32p_row07_traceSegment_093_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_093 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 486 121 122, g32p_row07_traceSegment_093_0486_0121, g32p_row07_traceSegment_093_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 729 15 15, g32p_row07_traceSegment_093_0729_0015, g32p_row07_traceSegment_093_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 774 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 759 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 759 15 15, g32p_row07_traceSegment_093_0759_0015, g32p_row07_traceSegment_093_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_093 729 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 729 30 30, g32p_row07_traceSegment_093_0729_0030, g32p_row07_traceSegment_093_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 789 15 15, g32p_row07_traceSegment_093_0789_0015, g32p_row07_traceSegment_093_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 819 15 16, g32p_row07_traceSegment_093_0819_0015, g32p_row07_traceSegment_093_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 789 30 31, g32p_row07_traceSegment_093_0789_0030, g32p_row07_traceSegment_093_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_093 729 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 729 60 61, g32p_row07_traceSegment_093_0729_0060, g32p_row07_traceSegment_093_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 850 15 15, g32p_row07_traceSegment_093_0850_0015, g32p_row07_traceSegment_093_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 880 15 16, g32p_row07_traceSegment_093_0880_0015, g32p_row07_traceSegment_093_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 850 30 31, g32p_row07_traceSegment_093_0850_0030, g32p_row07_traceSegment_093_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 911 15 15, g32p_row07_traceSegment_093_0911_0015, g32p_row07_traceSegment_093_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 941 15 16, g32p_row07_traceSegment_093_0941_0015, g32p_row07_traceSegment_093_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 911 30 31, g32p_row07_traceSegment_093_0911_0030, g32p_row07_traceSegment_093_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_093 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 850 61 61, g32p_row07_traceSegment_093_0850_0061, g32p_row07_traceSegment_093_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_093 729 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 729 121 122, g32p_row07_traceSegment_093_0729_0121, g32p_row07_traceSegment_093_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_093 486 486 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 486 243 243, g32p_row07_traceSegment_093_0486_0243, g32p_row07_traceSegment_093_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_093 0 972 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 0 486 486, g32p_row07_traceSegment_093_0000_0486, g32p_row07_traceSegment_093_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 972 15 15, g32p_row07_traceSegment_093_0972_0015, g32p_row07_traceSegment_093_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1002 15 15, g32p_row07_traceSegment_093_1002_0015, g32p_row07_traceSegment_093_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_093 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 972 30 30, g32p_row07_traceSegment_093_0972_0030, g32p_row07_traceSegment_093_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1032 15 15, g32p_row07_traceSegment_093_1032_0015, g32p_row07_traceSegment_093_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1062 15 16, g32p_row07_traceSegment_093_1062_0015, g32p_row07_traceSegment_093_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1032 30 31, g32p_row07_traceSegment_093_1032_0030, g32p_row07_traceSegment_093_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_093 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 972 60 61, g32p_row07_traceSegment_093_0972_0060, g32p_row07_traceSegment_093_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1093 15 15, g32p_row07_traceSegment_093_1093_0015, g32p_row07_traceSegment_093_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1123 15 16, g32p_row07_traceSegment_093_1123_0015, g32p_row07_traceSegment_093_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1093 30 31, g32p_row07_traceSegment_093_1093_0030, g32p_row07_traceSegment_093_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1154 15 15, g32p_row07_traceSegment_093_1154_0015, g32p_row07_traceSegment_093_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1184 15 16, g32p_row07_traceSegment_093_1184_0015, g32p_row07_traceSegment_093_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1154 30 31, g32p_row07_traceSegment_093_1154_0030, g32p_row07_traceSegment_093_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_093 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1093 61 61, g32p_row07_traceSegment_093_1093_0061, g32p_row07_traceSegment_093_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_093 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 972 121 122, g32p_row07_traceSegment_093_0972_0121, g32p_row07_traceSegment_093_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1215 15 15, g32p_row07_traceSegment_093_1215_0015, g32p_row07_traceSegment_093_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1245 15 15, g32p_row07_traceSegment_093_1245_0015, g32p_row07_traceSegment_093_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_093 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1215 30 30, g32p_row07_traceSegment_093_1215_0030, g32p_row07_traceSegment_093_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1275 15 15, g32p_row07_traceSegment_093_1275_0015, g32p_row07_traceSegment_093_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1305 15 16, g32p_row07_traceSegment_093_1305_0015, g32p_row07_traceSegment_093_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1275 30 31, g32p_row07_traceSegment_093_1275_0030, g32p_row07_traceSegment_093_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_093 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1215 60 61, g32p_row07_traceSegment_093_1215_0060, g32p_row07_traceSegment_093_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1336 15 15, g32p_row07_traceSegment_093_1336_0015, g32p_row07_traceSegment_093_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1366 15 16, g32p_row07_traceSegment_093_1366_0015, g32p_row07_traceSegment_093_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1336 30 31, g32p_row07_traceSegment_093_1336_0030, g32p_row07_traceSegment_093_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1397 15 15, g32p_row07_traceSegment_093_1397_0015, g32p_row07_traceSegment_093_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1427 15 16, g32p_row07_traceSegment_093_1427_0015, g32p_row07_traceSegment_093_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1397 30 31, g32p_row07_traceSegment_093_1397_0030, g32p_row07_traceSegment_093_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_093 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1336 61 61, g32p_row07_traceSegment_093_1336_0061, g32p_row07_traceSegment_093_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_093 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1215 121 122, g32p_row07_traceSegment_093_1215_0121, g32p_row07_traceSegment_093_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_093 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 972 243 243, g32p_row07_traceSegment_093_0972_0243, g32p_row07_traceSegment_093_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1458 15 15, g32p_row07_traceSegment_093_1458_0015, g32p_row07_traceSegment_093_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1488 15 15, g32p_row07_traceSegment_093_1488_0015, g32p_row07_traceSegment_093_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_093 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1458 30 30, g32p_row07_traceSegment_093_1458_0030, g32p_row07_traceSegment_093_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1518 15 15, g32p_row07_traceSegment_093_1518_0015, g32p_row07_traceSegment_093_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1548 15 16, g32p_row07_traceSegment_093_1548_0015, g32p_row07_traceSegment_093_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1518 30 31, g32p_row07_traceSegment_093_1518_0030, g32p_row07_traceSegment_093_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_093 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1458 60 61, g32p_row07_traceSegment_093_1458_0060, g32p_row07_traceSegment_093_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1579 15 15, g32p_row07_traceSegment_093_1579_0015, g32p_row07_traceSegment_093_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1609 15 16, g32p_row07_traceSegment_093_1609_0015, g32p_row07_traceSegment_093_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1579 30 31, g32p_row07_traceSegment_093_1579_0030, g32p_row07_traceSegment_093_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1640 15 15, g32p_row07_traceSegment_093_1640_0015, g32p_row07_traceSegment_093_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1670 15 16, g32p_row07_traceSegment_093_1670_0015, g32p_row07_traceSegment_093_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1640 30 31, g32p_row07_traceSegment_093_1640_0030, g32p_row07_traceSegment_093_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_093 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1579 61 61, g32p_row07_traceSegment_093_1579_0061, g32p_row07_traceSegment_093_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_093 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1458 121 122, g32p_row07_traceSegment_093_1458_0121, g32p_row07_traceSegment_093_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1701 15 15, g32p_row07_traceSegment_093_1701_0015, g32p_row07_traceSegment_093_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1731 15 15, g32p_row07_traceSegment_093_1731_0015, g32p_row07_traceSegment_093_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_093 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1701 30 30, g32p_row07_traceSegment_093_1701_0030, g32p_row07_traceSegment_093_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1761 15 15, g32p_row07_traceSegment_093_1761_0015, g32p_row07_traceSegment_093_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1791 15 16, g32p_row07_traceSegment_093_1791_0015, g32p_row07_traceSegment_093_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1761 30 31, g32p_row07_traceSegment_093_1761_0030, g32p_row07_traceSegment_093_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_093 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1701 60 61, g32p_row07_traceSegment_093_1701_0060, g32p_row07_traceSegment_093_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1822 15 15, g32p_row07_traceSegment_093_1822_0015, g32p_row07_traceSegment_093_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1852 15 16, g32p_row07_traceSegment_093_1852_0015, g32p_row07_traceSegment_093_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1822 30 31, g32p_row07_traceSegment_093_1822_0030, g32p_row07_traceSegment_093_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_093 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1883 15 15, g32p_row07_traceSegment_093_1883_0015, g32p_row07_traceSegment_093_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_093 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_093 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_093_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_093 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1913 15 16, g32p_row07_traceSegment_093_1913_0015, g32p_row07_traceSegment_093_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_093 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1883 30 31, g32p_row07_traceSegment_093_1883_0030, g32p_row07_traceSegment_093_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_093 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1822 61 61, g32p_row07_traceSegment_093_1822_0061, g32p_row07_traceSegment_093_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_093 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1701 121 122, g32p_row07_traceSegment_093_1701_0121, g32p_row07_traceSegment_093_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_093_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_093 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 1458 243 243, g32p_row07_traceSegment_093_1458_0243, g32p_row07_traceSegment_093_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_093 972 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 972 486 486, g32p_row07_traceSegment_093_0972_0486, g32p_row07_traceSegment_093_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_093_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_093 0 1944 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_093 0 972 972, g32p_row07_traceSegment_093_0000_0972, g32p_row07_traceSegment_093_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 93 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_093_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_095 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 95 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_095_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 15 15 = [2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 0 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 0 15 15, g32p_row07_traceSegment_095_0000_0015, g32p_row07_traceSegment_095_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 30 15 15, g32p_row07_traceSegment_095_0030_0015, g32p_row07_traceSegment_095_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_095 0 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 0 30 30, g32p_row07_traceSegment_095_0000_0030, g32p_row07_traceSegment_095_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 60 15 15, g32p_row07_traceSegment_095_0060_0015, g32p_row07_traceSegment_095_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 90 15 16, g32p_row07_traceSegment_095_0090_0015, g32p_row07_traceSegment_095_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 60 30 31, g32p_row07_traceSegment_095_0060_0030, g32p_row07_traceSegment_095_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_095 0 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 0 60 61, g32p_row07_traceSegment_095_0000_0060, g32p_row07_traceSegment_095_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 121 15 15, g32p_row07_traceSegment_095_0121_0015, g32p_row07_traceSegment_095_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 151 15 16, g32p_row07_traceSegment_095_0151_0015, g32p_row07_traceSegment_095_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 121 30 31, g32p_row07_traceSegment_095_0121_0030, g32p_row07_traceSegment_095_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 182 15 15, g32p_row07_traceSegment_095_0182_0015, g32p_row07_traceSegment_095_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 212 15 16, g32p_row07_traceSegment_095_0212_0015, g32p_row07_traceSegment_095_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 182 30 31, g32p_row07_traceSegment_095_0182_0030, g32p_row07_traceSegment_095_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_095 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 121 61 61, g32p_row07_traceSegment_095_0121_0061, g32p_row07_traceSegment_095_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_095 0 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 0 121 122, g32p_row07_traceSegment_095_0000_0121, g32p_row07_traceSegment_095_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 243 15 15, g32p_row07_traceSegment_095_0243_0015, g32p_row07_traceSegment_095_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 273 15 15, g32p_row07_traceSegment_095_0273_0015, g32p_row07_traceSegment_095_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_095 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 243 30 30, g32p_row07_traceSegment_095_0243_0030, g32p_row07_traceSegment_095_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 303 15 15, g32p_row07_traceSegment_095_0303_0015, g32p_row07_traceSegment_095_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 333 15 16, g32p_row07_traceSegment_095_0333_0015, g32p_row07_traceSegment_095_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 303 30 31, g32p_row07_traceSegment_095_0303_0030, g32p_row07_traceSegment_095_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_095 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 243 60 61, g32p_row07_traceSegment_095_0243_0060, g32p_row07_traceSegment_095_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 364 15 15, g32p_row07_traceSegment_095_0364_0015, g32p_row07_traceSegment_095_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 394 15 16, g32p_row07_traceSegment_095_0394_0015, g32p_row07_traceSegment_095_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 364 30 31, g32p_row07_traceSegment_095_0364_0030, g32p_row07_traceSegment_095_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 425 15 15, g32p_row07_traceSegment_095_0425_0015, g32p_row07_traceSegment_095_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 455 15 16, g32p_row07_traceSegment_095_0455_0015, g32p_row07_traceSegment_095_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 425 30 31, g32p_row07_traceSegment_095_0425_0030, g32p_row07_traceSegment_095_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_095 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 364 61 61, g32p_row07_traceSegment_095_0364_0061, g32p_row07_traceSegment_095_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_095 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 243 121 122, g32p_row07_traceSegment_095_0243_0121, g32p_row07_traceSegment_095_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_095 0 486 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 0 243 243, g32p_row07_traceSegment_095_0000_0243, g32p_row07_traceSegment_095_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 486 15 15, g32p_row07_traceSegment_095_0486_0015, g32p_row07_traceSegment_095_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 516 15 15, g32p_row07_traceSegment_095_0516_0015, g32p_row07_traceSegment_095_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_095 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 486 30 30, g32p_row07_traceSegment_095_0486_0030, g32p_row07_traceSegment_095_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 546 15 15, g32p_row07_traceSegment_095_0546_0015, g32p_row07_traceSegment_095_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 576 15 16, g32p_row07_traceSegment_095_0576_0015, g32p_row07_traceSegment_095_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 546 30 31, g32p_row07_traceSegment_095_0546_0030, g32p_row07_traceSegment_095_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_095 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 486 60 61, g32p_row07_traceSegment_095_0486_0060, g32p_row07_traceSegment_095_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 607 15 15, g32p_row07_traceSegment_095_0607_0015, g32p_row07_traceSegment_095_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 637 15 16, g32p_row07_traceSegment_095_0637_0015, g32p_row07_traceSegment_095_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 607 30 31, g32p_row07_traceSegment_095_0607_0030, g32p_row07_traceSegment_095_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 668 15 15, g32p_row07_traceSegment_095_0668_0015, g32p_row07_traceSegment_095_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 713 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 698 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 698 15 16, g32p_row07_traceSegment_095_0698_0015, g32p_row07_traceSegment_095_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 668 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 668 30 31, g32p_row07_traceSegment_095_0668_0030, g32p_row07_traceSegment_095_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_095 607 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 607 61 61, g32p_row07_traceSegment_095_0607_0061, g32p_row07_traceSegment_095_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_095 486 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 486 121 122, g32p_row07_traceSegment_095_0486_0121, g32p_row07_traceSegment_095_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 729 15 15, g32p_row07_traceSegment_095_0729_0015, g32p_row07_traceSegment_095_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 759 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 759 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 759 15 15, g32p_row07_traceSegment_095_0759_0015, g32p_row07_traceSegment_095_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_095 729 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 729 30 30, g32p_row07_traceSegment_095_0729_0030, g32p_row07_traceSegment_095_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 789 15 15, g32p_row07_traceSegment_095_0789_0015, g32p_row07_traceSegment_095_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 819 15 16, g32p_row07_traceSegment_095_0819_0015, g32p_row07_traceSegment_095_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 789 30 31, g32p_row07_traceSegment_095_0789_0030, g32p_row07_traceSegment_095_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_095 729 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 729 60 61, g32p_row07_traceSegment_095_0729_0060, g32p_row07_traceSegment_095_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 850 15 15, g32p_row07_traceSegment_095_0850_0015, g32p_row07_traceSegment_095_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 880 15 16, g32p_row07_traceSegment_095_0880_0015, g32p_row07_traceSegment_095_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 850 30 31, g32p_row07_traceSegment_095_0850_0030, g32p_row07_traceSegment_095_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 911 15 15, g32p_row07_traceSegment_095_0911_0015, g32p_row07_traceSegment_095_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 941 15 16, g32p_row07_traceSegment_095_0941_0015, g32p_row07_traceSegment_095_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 911 30 31, g32p_row07_traceSegment_095_0911_0030, g32p_row07_traceSegment_095_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_095 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 850 61 61, g32p_row07_traceSegment_095_0850_0061, g32p_row07_traceSegment_095_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_095 729 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 729 121 122, g32p_row07_traceSegment_095_0729_0121, g32p_row07_traceSegment_095_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_095 486 486 = [2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 486 243 243, g32p_row07_traceSegment_095_0486_0243, g32p_row07_traceSegment_095_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_095 0 972 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 0 486 486, g32p_row07_traceSegment_095_0000_0486, g32p_row07_traceSegment_095_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 972 15 15, g32p_row07_traceSegment_095_0972_0015, g32p_row07_traceSegment_095_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1002 15 15, g32p_row07_traceSegment_095_1002_0015, g32p_row07_traceSegment_095_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_095 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 972 30 30, g32p_row07_traceSegment_095_0972_0030, g32p_row07_traceSegment_095_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1032 15 15, g32p_row07_traceSegment_095_1032_0015, g32p_row07_traceSegment_095_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1062 15 16, g32p_row07_traceSegment_095_1062_0015, g32p_row07_traceSegment_095_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1032 30 31, g32p_row07_traceSegment_095_1032_0030, g32p_row07_traceSegment_095_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_095 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 972 60 61, g32p_row07_traceSegment_095_0972_0060, g32p_row07_traceSegment_095_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1093 15 15, g32p_row07_traceSegment_095_1093_0015, g32p_row07_traceSegment_095_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1123 15 16, g32p_row07_traceSegment_095_1123_0015, g32p_row07_traceSegment_095_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1093 30 31, g32p_row07_traceSegment_095_1093_0030, g32p_row07_traceSegment_095_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1154 15 15, g32p_row07_traceSegment_095_1154_0015, g32p_row07_traceSegment_095_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1184 15 16, g32p_row07_traceSegment_095_1184_0015, g32p_row07_traceSegment_095_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1154 30 31, g32p_row07_traceSegment_095_1154_0030, g32p_row07_traceSegment_095_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_095 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1093 61 61, g32p_row07_traceSegment_095_1093_0061, g32p_row07_traceSegment_095_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_095 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 972 121 122, g32p_row07_traceSegment_095_0972_0121, g32p_row07_traceSegment_095_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1215 15 15, g32p_row07_traceSegment_095_1215_0015, g32p_row07_traceSegment_095_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1245 15 15, g32p_row07_traceSegment_095_1245_0015, g32p_row07_traceSegment_095_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_095 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1215 30 30, g32p_row07_traceSegment_095_1215_0030, g32p_row07_traceSegment_095_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1275 15 15, g32p_row07_traceSegment_095_1275_0015, g32p_row07_traceSegment_095_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1305 15 16, g32p_row07_traceSegment_095_1305_0015, g32p_row07_traceSegment_095_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1275 30 31, g32p_row07_traceSegment_095_1275_0030, g32p_row07_traceSegment_095_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_095 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1215 60 61, g32p_row07_traceSegment_095_1215_0060, g32p_row07_traceSegment_095_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1336 15 15, g32p_row07_traceSegment_095_1336_0015, g32p_row07_traceSegment_095_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1366 15 16, g32p_row07_traceSegment_095_1366_0015, g32p_row07_traceSegment_095_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1336 30 31, g32p_row07_traceSegment_095_1336_0030, g32p_row07_traceSegment_095_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1397 15 15, g32p_row07_traceSegment_095_1397_0015, g32p_row07_traceSegment_095_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1427 15 16, g32p_row07_traceSegment_095_1427_0015, g32p_row07_traceSegment_095_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1397 30 31, g32p_row07_traceSegment_095_1397_0030, g32p_row07_traceSegment_095_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_095 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1336 61 61, g32p_row07_traceSegment_095_1336_0061, g32p_row07_traceSegment_095_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_095 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1215 121 122, g32p_row07_traceSegment_095_1215_0121, g32p_row07_traceSegment_095_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_095 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 972 243 243, g32p_row07_traceSegment_095_0972_0243, g32p_row07_traceSegment_095_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1458 15 15, g32p_row07_traceSegment_095_1458_0015, g32p_row07_traceSegment_095_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1488 15 15, g32p_row07_traceSegment_095_1488_0015, g32p_row07_traceSegment_095_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_095 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1458 30 30, g32p_row07_traceSegment_095_1458_0030, g32p_row07_traceSegment_095_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1518 15 15, g32p_row07_traceSegment_095_1518_0015, g32p_row07_traceSegment_095_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1548 15 16, g32p_row07_traceSegment_095_1548_0015, g32p_row07_traceSegment_095_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1518 30 31, g32p_row07_traceSegment_095_1518_0030, g32p_row07_traceSegment_095_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_095 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1458 60 61, g32p_row07_traceSegment_095_1458_0060, g32p_row07_traceSegment_095_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1579 15 15, g32p_row07_traceSegment_095_1579_0015, g32p_row07_traceSegment_095_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1609 15 16, g32p_row07_traceSegment_095_1609_0015, g32p_row07_traceSegment_095_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1579 30 31, g32p_row07_traceSegment_095_1579_0030, g32p_row07_traceSegment_095_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1640 15 15, g32p_row07_traceSegment_095_1640_0015, g32p_row07_traceSegment_095_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1670 15 16, g32p_row07_traceSegment_095_1670_0015, g32p_row07_traceSegment_095_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1640 30 31, g32p_row07_traceSegment_095_1640_0030, g32p_row07_traceSegment_095_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_095 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1579 61 61, g32p_row07_traceSegment_095_1579_0061, g32p_row07_traceSegment_095_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_095 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1458 121 122, g32p_row07_traceSegment_095_1458_0121, g32p_row07_traceSegment_095_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1701 15 15, g32p_row07_traceSegment_095_1701_0015, g32p_row07_traceSegment_095_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1731 15 15, g32p_row07_traceSegment_095_1731_0015, g32p_row07_traceSegment_095_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_095 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1701 30 30, g32p_row07_traceSegment_095_1701_0030, g32p_row07_traceSegment_095_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1761 15 15, g32p_row07_traceSegment_095_1761_0015, g32p_row07_traceSegment_095_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1791 15 16, g32p_row07_traceSegment_095_1791_0015, g32p_row07_traceSegment_095_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1761 30 31, g32p_row07_traceSegment_095_1761_0030, g32p_row07_traceSegment_095_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_095 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1701 60 61, g32p_row07_traceSegment_095_1701_0060, g32p_row07_traceSegment_095_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1822 15 15, g32p_row07_traceSegment_095_1822_0015, g32p_row07_traceSegment_095_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1852 15 16, g32p_row07_traceSegment_095_1852_0015, g32p_row07_traceSegment_095_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1822 30 31, g32p_row07_traceSegment_095_1822_0030, g32p_row07_traceSegment_095_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_095 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1883 15 15, g32p_row07_traceSegment_095_1883_0015, g32p_row07_traceSegment_095_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_095 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_095 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_095_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_095 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1913 15 16, g32p_row07_traceSegment_095_1913_0015, g32p_row07_traceSegment_095_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_095 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1883 30 31, g32p_row07_traceSegment_095_1883_0030, g32p_row07_traceSegment_095_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_095 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1822 61 61, g32p_row07_traceSegment_095_1822_0061, g32p_row07_traceSegment_095_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_095 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1701 121 122, g32p_row07_traceSegment_095_1701_0121, g32p_row07_traceSegment_095_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_095_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_095 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 1458 243 243, g32p_row07_traceSegment_095_1458_0243, g32p_row07_traceSegment_095_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_095 972 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 972 486 486, g32p_row07_traceSegment_095_0972_0486, g32p_row07_traceSegment_095_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_095_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_095 0 1944 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_095 0 972 972, g32p_row07_traceSegment_095_0000_0972, g32p_row07_traceSegment_095_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 95 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_095_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_096_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 0 15 15, g32p_row07_traceSegment_096_0000_0015, g32p_row07_traceSegment_096_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 30 15 15, g32p_row07_traceSegment_096_0030_0015, g32p_row07_traceSegment_096_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_096 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 0 30 30, g32p_row07_traceSegment_096_0000_0030, g32p_row07_traceSegment_096_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 60 15 15, g32p_row07_traceSegment_096_0060_0015, g32p_row07_traceSegment_096_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 90 15 16, g32p_row07_traceSegment_096_0090_0015, g32p_row07_traceSegment_096_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 60 30 31, g32p_row07_traceSegment_096_0060_0030, g32p_row07_traceSegment_096_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_096 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 0 60 61, g32p_row07_traceSegment_096_0000_0060, g32p_row07_traceSegment_096_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 121 15 15, g32p_row07_traceSegment_096_0121_0015, g32p_row07_traceSegment_096_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 151 15 16, g32p_row07_traceSegment_096_0151_0015, g32p_row07_traceSegment_096_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 121 30 31, g32p_row07_traceSegment_096_0121_0030, g32p_row07_traceSegment_096_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 182 15 15, g32p_row07_traceSegment_096_0182_0015, g32p_row07_traceSegment_096_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 212 15 16, g32p_row07_traceSegment_096_0212_0015, g32p_row07_traceSegment_096_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 182 30 31, g32p_row07_traceSegment_096_0182_0030, g32p_row07_traceSegment_096_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_096 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 121 61 61, g32p_row07_traceSegment_096_0121_0061, g32p_row07_traceSegment_096_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_096 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 0 121 122, g32p_row07_traceSegment_096_0000_0121, g32p_row07_traceSegment_096_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 243 15 15, g32p_row07_traceSegment_096_0243_0015, g32p_row07_traceSegment_096_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 273 15 15, g32p_row07_traceSegment_096_0273_0015, g32p_row07_traceSegment_096_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_096 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 243 30 30, g32p_row07_traceSegment_096_0243_0030, g32p_row07_traceSegment_096_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 303 15 15, g32p_row07_traceSegment_096_0303_0015, g32p_row07_traceSegment_096_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 333 15 16, g32p_row07_traceSegment_096_0333_0015, g32p_row07_traceSegment_096_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 303 30 31, g32p_row07_traceSegment_096_0303_0030, g32p_row07_traceSegment_096_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_096 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 243 60 61, g32p_row07_traceSegment_096_0243_0060, g32p_row07_traceSegment_096_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 364 15 15, g32p_row07_traceSegment_096_0364_0015, g32p_row07_traceSegment_096_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 394 15 16, g32p_row07_traceSegment_096_0394_0015, g32p_row07_traceSegment_096_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 364 30 31, g32p_row07_traceSegment_096_0364_0030, g32p_row07_traceSegment_096_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 425 15 15, g32p_row07_traceSegment_096_0425_0015, g32p_row07_traceSegment_096_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 455 15 16, g32p_row07_traceSegment_096_0455_0015, g32p_row07_traceSegment_096_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 425 30 31, g32p_row07_traceSegment_096_0425_0030, g32p_row07_traceSegment_096_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_096 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 364 61 61, g32p_row07_traceSegment_096_0364_0061, g32p_row07_traceSegment_096_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_096 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 243 121 122, g32p_row07_traceSegment_096_0243_0121, g32p_row07_traceSegment_096_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_096 0 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 0 243 243, g32p_row07_traceSegment_096_0000_0243, g32p_row07_traceSegment_096_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 486 15 15, g32p_row07_traceSegment_096_0486_0015, g32p_row07_traceSegment_096_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 516 15 15, g32p_row07_traceSegment_096_0516_0015, g32p_row07_traceSegment_096_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_096 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 486 30 30, g32p_row07_traceSegment_096_0486_0030, g32p_row07_traceSegment_096_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 546 15 15, g32p_row07_traceSegment_096_0546_0015, g32p_row07_traceSegment_096_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 576 15 16, g32p_row07_traceSegment_096_0576_0015, g32p_row07_traceSegment_096_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 546 30 31, g32p_row07_traceSegment_096_0546_0030, g32p_row07_traceSegment_096_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_096 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 486 60 61, g32p_row07_traceSegment_096_0486_0060, g32p_row07_traceSegment_096_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 607 15 15, g32p_row07_traceSegment_096_0607_0015, g32p_row07_traceSegment_096_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 637 15 16, g32p_row07_traceSegment_096_0637_0015, g32p_row07_traceSegment_096_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 607 30 31, g32p_row07_traceSegment_096_0607_0030, g32p_row07_traceSegment_096_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 668 15 15, g32p_row07_traceSegment_096_0668_0015, g32p_row07_traceSegment_096_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 698 15 16, g32p_row07_traceSegment_096_0698_0015, g32p_row07_traceSegment_096_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 668 30 31, g32p_row07_traceSegment_096_0668_0030, g32p_row07_traceSegment_096_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_096 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 607 61 61, g32p_row07_traceSegment_096_0607_0061, g32p_row07_traceSegment_096_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_096 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 486 121 122, g32p_row07_traceSegment_096_0486_0121, g32p_row07_traceSegment_096_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 729 15 15, g32p_row07_traceSegment_096_0729_0015, g32p_row07_traceSegment_096_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 759 15 15, g32p_row07_traceSegment_096_0759_0015, g32p_row07_traceSegment_096_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_096 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 729 30 30, g32p_row07_traceSegment_096_0729_0030, g32p_row07_traceSegment_096_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 789 15 15, g32p_row07_traceSegment_096_0789_0015, g32p_row07_traceSegment_096_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 819 15 16, g32p_row07_traceSegment_096_0819_0015, g32p_row07_traceSegment_096_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 789 30 31, g32p_row07_traceSegment_096_0789_0030, g32p_row07_traceSegment_096_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_096 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 729 60 61, g32p_row07_traceSegment_096_0729_0060, g32p_row07_traceSegment_096_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 850 15 15, g32p_row07_traceSegment_096_0850_0015, g32p_row07_traceSegment_096_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 880 15 16, g32p_row07_traceSegment_096_0880_0015, g32p_row07_traceSegment_096_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 850 30 31, g32p_row07_traceSegment_096_0850_0030, g32p_row07_traceSegment_096_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 911 15 15, g32p_row07_traceSegment_096_0911_0015, g32p_row07_traceSegment_096_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 941 15 16, g32p_row07_traceSegment_096_0941_0015, g32p_row07_traceSegment_096_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 911 30 31, g32p_row07_traceSegment_096_0911_0030, g32p_row07_traceSegment_096_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_096 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 850 61 61, g32p_row07_traceSegment_096_0850_0061, g32p_row07_traceSegment_096_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_096 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 729 121 122, g32p_row07_traceSegment_096_0729_0121, g32p_row07_traceSegment_096_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_096 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 486 243 243, g32p_row07_traceSegment_096_0486_0243, g32p_row07_traceSegment_096_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_096 0 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 0 486 486, g32p_row07_traceSegment_096_0000_0486, g32p_row07_traceSegment_096_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 972 15 15, g32p_row07_traceSegment_096_0972_0015, g32p_row07_traceSegment_096_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1002 15 15, g32p_row07_traceSegment_096_1002_0015, g32p_row07_traceSegment_096_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_096 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 972 30 30, g32p_row07_traceSegment_096_0972_0030, g32p_row07_traceSegment_096_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1032 15 15, g32p_row07_traceSegment_096_1032_0015, g32p_row07_traceSegment_096_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1062 15 16, g32p_row07_traceSegment_096_1062_0015, g32p_row07_traceSegment_096_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1032 30 31, g32p_row07_traceSegment_096_1032_0030, g32p_row07_traceSegment_096_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_096 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 972 60 61, g32p_row07_traceSegment_096_0972_0060, g32p_row07_traceSegment_096_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1093 15 15, g32p_row07_traceSegment_096_1093_0015, g32p_row07_traceSegment_096_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1123 15 16, g32p_row07_traceSegment_096_1123_0015, g32p_row07_traceSegment_096_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1093 30 31, g32p_row07_traceSegment_096_1093_0030, g32p_row07_traceSegment_096_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1154 15 15, g32p_row07_traceSegment_096_1154_0015, g32p_row07_traceSegment_096_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1184 15 16, g32p_row07_traceSegment_096_1184_0015, g32p_row07_traceSegment_096_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1154 30 31, g32p_row07_traceSegment_096_1154_0030, g32p_row07_traceSegment_096_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_096 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1093 61 61, g32p_row07_traceSegment_096_1093_0061, g32p_row07_traceSegment_096_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_096 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 972 121 122, g32p_row07_traceSegment_096_0972_0121, g32p_row07_traceSegment_096_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1215 15 15, g32p_row07_traceSegment_096_1215_0015, g32p_row07_traceSegment_096_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1245 15 15, g32p_row07_traceSegment_096_1245_0015, g32p_row07_traceSegment_096_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_096 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1215 30 30, g32p_row07_traceSegment_096_1215_0030, g32p_row07_traceSegment_096_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1290 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1275 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1275 15 15, g32p_row07_traceSegment_096_1275_0015, g32p_row07_traceSegment_096_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1305 15 16, g32p_row07_traceSegment_096_1305_0015, g32p_row07_traceSegment_096_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1275 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1275 30 31, g32p_row07_traceSegment_096_1275_0030, g32p_row07_traceSegment_096_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_096 1215 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1215 60 61, g32p_row07_traceSegment_096_1215_0060, g32p_row07_traceSegment_096_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1336 15 15, g32p_row07_traceSegment_096_1336_0015, g32p_row07_traceSegment_096_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1366 15 16, g32p_row07_traceSegment_096_1366_0015, g32p_row07_traceSegment_096_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1336 30 31, g32p_row07_traceSegment_096_1336_0030, g32p_row07_traceSegment_096_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1397 15 15, g32p_row07_traceSegment_096_1397_0015, g32p_row07_traceSegment_096_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1427 15 16, g32p_row07_traceSegment_096_1427_0015, g32p_row07_traceSegment_096_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1397 30 31, g32p_row07_traceSegment_096_1397_0030, g32p_row07_traceSegment_096_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_096 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1336 61 61, g32p_row07_traceSegment_096_1336_0061, g32p_row07_traceSegment_096_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_096 1215 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1215 121 122, g32p_row07_traceSegment_096_1215_0121, g32p_row07_traceSegment_096_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_096 972 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 972 243 243, g32p_row07_traceSegment_096_0972_0243, g32p_row07_traceSegment_096_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1458 15 15, g32p_row07_traceSegment_096_1458_0015, g32p_row07_traceSegment_096_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1488 15 15, g32p_row07_traceSegment_096_1488_0015, g32p_row07_traceSegment_096_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_096 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1458 30 30, g32p_row07_traceSegment_096_1458_0030, g32p_row07_traceSegment_096_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1518 15 15, g32p_row07_traceSegment_096_1518_0015, g32p_row07_traceSegment_096_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1548 15 16, g32p_row07_traceSegment_096_1548_0015, g32p_row07_traceSegment_096_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1518 30 31, g32p_row07_traceSegment_096_1518_0030, g32p_row07_traceSegment_096_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_096 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1458 60 61, g32p_row07_traceSegment_096_1458_0060, g32p_row07_traceSegment_096_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1579 15 15, g32p_row07_traceSegment_096_1579_0015, g32p_row07_traceSegment_096_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1609 15 16, g32p_row07_traceSegment_096_1609_0015, g32p_row07_traceSegment_096_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1579 30 31, g32p_row07_traceSegment_096_1579_0030, g32p_row07_traceSegment_096_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1640 15 15, g32p_row07_traceSegment_096_1640_0015, g32p_row07_traceSegment_096_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1670 15 16, g32p_row07_traceSegment_096_1670_0015, g32p_row07_traceSegment_096_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1640 30 31, g32p_row07_traceSegment_096_1640_0030, g32p_row07_traceSegment_096_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_096 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1579 61 61, g32p_row07_traceSegment_096_1579_0061, g32p_row07_traceSegment_096_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_096 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1458 121 122, g32p_row07_traceSegment_096_1458_0121, g32p_row07_traceSegment_096_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1701 15 15, g32p_row07_traceSegment_096_1701_0015, g32p_row07_traceSegment_096_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1731 15 15, g32p_row07_traceSegment_096_1731_0015, g32p_row07_traceSegment_096_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_096 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1701 30 30, g32p_row07_traceSegment_096_1701_0030, g32p_row07_traceSegment_096_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1761 15 15, g32p_row07_traceSegment_096_1761_0015, g32p_row07_traceSegment_096_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1791 15 16, g32p_row07_traceSegment_096_1791_0015, g32p_row07_traceSegment_096_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1761 30 31, g32p_row07_traceSegment_096_1761_0030, g32p_row07_traceSegment_096_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_096 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1701 60 61, g32p_row07_traceSegment_096_1701_0060, g32p_row07_traceSegment_096_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1822 15 15, g32p_row07_traceSegment_096_1822_0015, g32p_row07_traceSegment_096_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1852 15 16, g32p_row07_traceSegment_096_1852_0015, g32p_row07_traceSegment_096_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1822 30 31, g32p_row07_traceSegment_096_1822_0030, g32p_row07_traceSegment_096_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_096 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1883 15 15, g32p_row07_traceSegment_096_1883_0015, g32p_row07_traceSegment_096_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_096 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_096 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_096_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_096 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1913 15 16, g32p_row07_traceSegment_096_1913_0015, g32p_row07_traceSegment_096_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_096 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1883 30 31, g32p_row07_traceSegment_096_1883_0030, g32p_row07_traceSegment_096_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_096 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1822 61 61, g32p_row07_traceSegment_096_1822_0061, g32p_row07_traceSegment_096_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_096 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1701 121 122, g32p_row07_traceSegment_096_1701_0121, g32p_row07_traceSegment_096_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_096_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_096 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 1458 243 243, g32p_row07_traceSegment_096_1458_0243, g32p_row07_traceSegment_096_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_096 972 972 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 972 486 486, g32p_row07_traceSegment_096_0972_0486, g32p_row07_traceSegment_096_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_096_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_096 0 1944 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_096 0 972 972, g32p_row07_traceSegment_096_0000_0972, g32p_row07_traceSegment_096_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 96 = [0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_096_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_097_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 0 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 0 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 0 15 15, g32p_row07_traceSegment_097_0000_0015, g32p_row07_traceSegment_097_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 30 15 15, g32p_row07_traceSegment_097_0030_0015, g32p_row07_traceSegment_097_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_097 0 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 0 30 30, g32p_row07_traceSegment_097_0000_0030, g32p_row07_traceSegment_097_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 60 15 15, g32p_row07_traceSegment_097_0060_0015, g32p_row07_traceSegment_097_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 90 15 16, g32p_row07_traceSegment_097_0090_0015, g32p_row07_traceSegment_097_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 60 30 31, g32p_row07_traceSegment_097_0060_0030, g32p_row07_traceSegment_097_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_097 0 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 0 60 61, g32p_row07_traceSegment_097_0000_0060, g32p_row07_traceSegment_097_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 121 15 15, g32p_row07_traceSegment_097_0121_0015, g32p_row07_traceSegment_097_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 151 15 16, g32p_row07_traceSegment_097_0151_0015, g32p_row07_traceSegment_097_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 121 30 31, g32p_row07_traceSegment_097_0121_0030, g32p_row07_traceSegment_097_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 182 15 15, g32p_row07_traceSegment_097_0182_0015, g32p_row07_traceSegment_097_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 212 15 16, g32p_row07_traceSegment_097_0212_0015, g32p_row07_traceSegment_097_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 182 30 31, g32p_row07_traceSegment_097_0182_0030, g32p_row07_traceSegment_097_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_097 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 121 61 61, g32p_row07_traceSegment_097_0121_0061, g32p_row07_traceSegment_097_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_097 0 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 0 121 122, g32p_row07_traceSegment_097_0000_0121, g32p_row07_traceSegment_097_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 243 15 15, g32p_row07_traceSegment_097_0243_0015, g32p_row07_traceSegment_097_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 273 15 15, g32p_row07_traceSegment_097_0273_0015, g32p_row07_traceSegment_097_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_097 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 243 30 30, g32p_row07_traceSegment_097_0243_0030, g32p_row07_traceSegment_097_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 303 15 15, g32p_row07_traceSegment_097_0303_0015, g32p_row07_traceSegment_097_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 333 15 16, g32p_row07_traceSegment_097_0333_0015, g32p_row07_traceSegment_097_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 303 30 31, g32p_row07_traceSegment_097_0303_0030, g32p_row07_traceSegment_097_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_097 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 243 60 61, g32p_row07_traceSegment_097_0243_0060, g32p_row07_traceSegment_097_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 364 15 15, g32p_row07_traceSegment_097_0364_0015, g32p_row07_traceSegment_097_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 394 15 16, g32p_row07_traceSegment_097_0394_0015, g32p_row07_traceSegment_097_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 364 30 31, g32p_row07_traceSegment_097_0364_0030, g32p_row07_traceSegment_097_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 425 15 15, g32p_row07_traceSegment_097_0425_0015, g32p_row07_traceSegment_097_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 455 15 16, g32p_row07_traceSegment_097_0455_0015, g32p_row07_traceSegment_097_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 425 30 31, g32p_row07_traceSegment_097_0425_0030, g32p_row07_traceSegment_097_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_097 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 364 61 61, g32p_row07_traceSegment_097_0364_0061, g32p_row07_traceSegment_097_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_097 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 243 121 122, g32p_row07_traceSegment_097_0243_0121, g32p_row07_traceSegment_097_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_097 0 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 0 243 243, g32p_row07_traceSegment_097_0000_0243, g32p_row07_traceSegment_097_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 486 15 15, g32p_row07_traceSegment_097_0486_0015, g32p_row07_traceSegment_097_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 516 15 15, g32p_row07_traceSegment_097_0516_0015, g32p_row07_traceSegment_097_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_097 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 486 30 30, g32p_row07_traceSegment_097_0486_0030, g32p_row07_traceSegment_097_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 546 15 15, g32p_row07_traceSegment_097_0546_0015, g32p_row07_traceSegment_097_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 576 15 16, g32p_row07_traceSegment_097_0576_0015, g32p_row07_traceSegment_097_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 546 30 31, g32p_row07_traceSegment_097_0546_0030, g32p_row07_traceSegment_097_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_097 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 486 60 61, g32p_row07_traceSegment_097_0486_0060, g32p_row07_traceSegment_097_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 607 15 15, g32p_row07_traceSegment_097_0607_0015, g32p_row07_traceSegment_097_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 637 15 16, g32p_row07_traceSegment_097_0637_0015, g32p_row07_traceSegment_097_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 607 30 31, g32p_row07_traceSegment_097_0607_0030, g32p_row07_traceSegment_097_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 668 15 15, g32p_row07_traceSegment_097_0668_0015, g32p_row07_traceSegment_097_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 698 15 16, g32p_row07_traceSegment_097_0698_0015, g32p_row07_traceSegment_097_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 668 30 31, g32p_row07_traceSegment_097_0668_0030, g32p_row07_traceSegment_097_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_097 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 607 61 61, g32p_row07_traceSegment_097_0607_0061, g32p_row07_traceSegment_097_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_097 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 486 121 122, g32p_row07_traceSegment_097_0486_0121, g32p_row07_traceSegment_097_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 729 15 15, g32p_row07_traceSegment_097_0729_0015, g32p_row07_traceSegment_097_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 759 15 15, g32p_row07_traceSegment_097_0759_0015, g32p_row07_traceSegment_097_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_097 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 729 30 30, g32p_row07_traceSegment_097_0729_0030, g32p_row07_traceSegment_097_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 789 15 15, g32p_row07_traceSegment_097_0789_0015, g32p_row07_traceSegment_097_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 819 15 16, g32p_row07_traceSegment_097_0819_0015, g32p_row07_traceSegment_097_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 789 30 31, g32p_row07_traceSegment_097_0789_0030, g32p_row07_traceSegment_097_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_097 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 729 60 61, g32p_row07_traceSegment_097_0729_0060, g32p_row07_traceSegment_097_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 850 15 15, g32p_row07_traceSegment_097_0850_0015, g32p_row07_traceSegment_097_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 880 15 16, g32p_row07_traceSegment_097_0880_0015, g32p_row07_traceSegment_097_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 850 30 31, g32p_row07_traceSegment_097_0850_0030, g32p_row07_traceSegment_097_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 911 15 15, g32p_row07_traceSegment_097_0911_0015, g32p_row07_traceSegment_097_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 941 15 16, g32p_row07_traceSegment_097_0941_0015, g32p_row07_traceSegment_097_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 911 30 31, g32p_row07_traceSegment_097_0911_0030, g32p_row07_traceSegment_097_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_097 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 850 61 61, g32p_row07_traceSegment_097_0850_0061, g32p_row07_traceSegment_097_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_097 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 729 121 122, g32p_row07_traceSegment_097_0729_0121, g32p_row07_traceSegment_097_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_097 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 486 243 243, g32p_row07_traceSegment_097_0486_0243, g32p_row07_traceSegment_097_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_097 0 972 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 0 486 486, g32p_row07_traceSegment_097_0000_0486, g32p_row07_traceSegment_097_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 972 15 15, g32p_row07_traceSegment_097_0972_0015, g32p_row07_traceSegment_097_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1002 15 15, g32p_row07_traceSegment_097_1002_0015, g32p_row07_traceSegment_097_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_097 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 972 30 30, g32p_row07_traceSegment_097_0972_0030, g32p_row07_traceSegment_097_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1032 15 15, g32p_row07_traceSegment_097_1032_0015, g32p_row07_traceSegment_097_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1062 15 16, g32p_row07_traceSegment_097_1062_0015, g32p_row07_traceSegment_097_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1032 30 31, g32p_row07_traceSegment_097_1032_0030, g32p_row07_traceSegment_097_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_097 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 972 60 61, g32p_row07_traceSegment_097_0972_0060, g32p_row07_traceSegment_097_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1093 15 15, g32p_row07_traceSegment_097_1093_0015, g32p_row07_traceSegment_097_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1123 15 16, g32p_row07_traceSegment_097_1123_0015, g32p_row07_traceSegment_097_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1093 30 31, g32p_row07_traceSegment_097_1093_0030, g32p_row07_traceSegment_097_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1154 15 15, g32p_row07_traceSegment_097_1154_0015, g32p_row07_traceSegment_097_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1184 15 16, g32p_row07_traceSegment_097_1184_0015, g32p_row07_traceSegment_097_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1154 30 31, g32p_row07_traceSegment_097_1154_0030, g32p_row07_traceSegment_097_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_097 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1093 61 61, g32p_row07_traceSegment_097_1093_0061, g32p_row07_traceSegment_097_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_097 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 972 121 122, g32p_row07_traceSegment_097_0972_0121, g32p_row07_traceSegment_097_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1215 15 15, g32p_row07_traceSegment_097_1215_0015, g32p_row07_traceSegment_097_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1245 15 15, g32p_row07_traceSegment_097_1245_0015, g32p_row07_traceSegment_097_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_097 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1215 30 30, g32p_row07_traceSegment_097_1215_0030, g32p_row07_traceSegment_097_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1275 15 15, g32p_row07_traceSegment_097_1275_0015, g32p_row07_traceSegment_097_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1305 15 16, g32p_row07_traceSegment_097_1305_0015, g32p_row07_traceSegment_097_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1275 30 31, g32p_row07_traceSegment_097_1275_0030, g32p_row07_traceSegment_097_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_097 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1215 60 61, g32p_row07_traceSegment_097_1215_0060, g32p_row07_traceSegment_097_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1336 15 15, g32p_row07_traceSegment_097_1336_0015, g32p_row07_traceSegment_097_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1366 15 16, g32p_row07_traceSegment_097_1366_0015, g32p_row07_traceSegment_097_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1336 30 31, g32p_row07_traceSegment_097_1336_0030, g32p_row07_traceSegment_097_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1397 15 15, g32p_row07_traceSegment_097_1397_0015, g32p_row07_traceSegment_097_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1427 15 16, g32p_row07_traceSegment_097_1427_0015, g32p_row07_traceSegment_097_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1397 30 31, g32p_row07_traceSegment_097_1397_0030, g32p_row07_traceSegment_097_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_097 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1336 61 61, g32p_row07_traceSegment_097_1336_0061, g32p_row07_traceSegment_097_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_097 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1215 121 122, g32p_row07_traceSegment_097_1215_0121, g32p_row07_traceSegment_097_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_097 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 972 243 243, g32p_row07_traceSegment_097_0972_0243, g32p_row07_traceSegment_097_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1458 15 15, g32p_row07_traceSegment_097_1458_0015, g32p_row07_traceSegment_097_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1488 15 15, g32p_row07_traceSegment_097_1488_0015, g32p_row07_traceSegment_097_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_097 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1458 30 30, g32p_row07_traceSegment_097_1458_0030, g32p_row07_traceSegment_097_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1518 15 15, g32p_row07_traceSegment_097_1518_0015, g32p_row07_traceSegment_097_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1548 15 16, g32p_row07_traceSegment_097_1548_0015, g32p_row07_traceSegment_097_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1518 30 31, g32p_row07_traceSegment_097_1518_0030, g32p_row07_traceSegment_097_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_097 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1458 60 61, g32p_row07_traceSegment_097_1458_0060, g32p_row07_traceSegment_097_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1579 15 15, g32p_row07_traceSegment_097_1579_0015, g32p_row07_traceSegment_097_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1609 15 16, g32p_row07_traceSegment_097_1609_0015, g32p_row07_traceSegment_097_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1579 30 31, g32p_row07_traceSegment_097_1579_0030, g32p_row07_traceSegment_097_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1640 15 15, g32p_row07_traceSegment_097_1640_0015, g32p_row07_traceSegment_097_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1670 15 16, g32p_row07_traceSegment_097_1670_0015, g32p_row07_traceSegment_097_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1640 30 31, g32p_row07_traceSegment_097_1640_0030, g32p_row07_traceSegment_097_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_097 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1579 61 61, g32p_row07_traceSegment_097_1579_0061, g32p_row07_traceSegment_097_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_097 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1458 121 122, g32p_row07_traceSegment_097_1458_0121, g32p_row07_traceSegment_097_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1701 15 15, g32p_row07_traceSegment_097_1701_0015, g32p_row07_traceSegment_097_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1731 15 15, g32p_row07_traceSegment_097_1731_0015, g32p_row07_traceSegment_097_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_097 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1701 30 30, g32p_row07_traceSegment_097_1701_0030, g32p_row07_traceSegment_097_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1761 15 15, g32p_row07_traceSegment_097_1761_0015, g32p_row07_traceSegment_097_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1791 15 16, g32p_row07_traceSegment_097_1791_0015, g32p_row07_traceSegment_097_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1761 30 31, g32p_row07_traceSegment_097_1761_0030, g32p_row07_traceSegment_097_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_097 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1701 60 61, g32p_row07_traceSegment_097_1701_0060, g32p_row07_traceSegment_097_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1822 15 15, g32p_row07_traceSegment_097_1822_0015, g32p_row07_traceSegment_097_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1852 15 16, g32p_row07_traceSegment_097_1852_0015, g32p_row07_traceSegment_097_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1822 30 31, g32p_row07_traceSegment_097_1822_0030, g32p_row07_traceSegment_097_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_097 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1883 15 15, g32p_row07_traceSegment_097_1883_0015, g32p_row07_traceSegment_097_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_097 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_097 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_097_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_097 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1913 15 16, g32p_row07_traceSegment_097_1913_0015, g32p_row07_traceSegment_097_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_097 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1883 30 31, g32p_row07_traceSegment_097_1883_0030, g32p_row07_traceSegment_097_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_097 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1822 61 61, g32p_row07_traceSegment_097_1822_0061, g32p_row07_traceSegment_097_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_097 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1701 121 122, g32p_row07_traceSegment_097_1701_0121, g32p_row07_traceSegment_097_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_097_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_097 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 1458 243 243, g32p_row07_traceSegment_097_1458_0243, g32p_row07_traceSegment_097_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_097 972 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 972 486 486, g32p_row07_traceSegment_097_0972_0486, g32p_row07_traceSegment_097_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_097_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_097 0 1944 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_097 0 972 972, g32p_row07_traceSegment_097_0000_0972, g32p_row07_traceSegment_097_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 97 = [0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_097_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_098 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 98 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_098_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 0 15 15, g32p_row07_traceSegment_098_0000_0015, g32p_row07_traceSegment_098_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 30 15 15, g32p_row07_traceSegment_098_0030_0015, g32p_row07_traceSegment_098_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_098 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 0 30 30, g32p_row07_traceSegment_098_0000_0030, g32p_row07_traceSegment_098_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 60 15 15, g32p_row07_traceSegment_098_0060_0015, g32p_row07_traceSegment_098_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 90 15 16, g32p_row07_traceSegment_098_0090_0015, g32p_row07_traceSegment_098_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 60 30 31, g32p_row07_traceSegment_098_0060_0030, g32p_row07_traceSegment_098_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_098 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 0 60 61, g32p_row07_traceSegment_098_0000_0060, g32p_row07_traceSegment_098_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 121 15 15, g32p_row07_traceSegment_098_0121_0015, g32p_row07_traceSegment_098_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 151 15 16, g32p_row07_traceSegment_098_0151_0015, g32p_row07_traceSegment_098_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 121 30 31, g32p_row07_traceSegment_098_0121_0030, g32p_row07_traceSegment_098_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 182 15 15, g32p_row07_traceSegment_098_0182_0015, g32p_row07_traceSegment_098_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 212 15 16, g32p_row07_traceSegment_098_0212_0015, g32p_row07_traceSegment_098_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 182 30 31, g32p_row07_traceSegment_098_0182_0030, g32p_row07_traceSegment_098_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_098 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 121 61 61, g32p_row07_traceSegment_098_0121_0061, g32p_row07_traceSegment_098_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_098 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 0 121 122, g32p_row07_traceSegment_098_0000_0121, g32p_row07_traceSegment_098_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 243 15 15, g32p_row07_traceSegment_098_0243_0015, g32p_row07_traceSegment_098_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 273 15 15, g32p_row07_traceSegment_098_0273_0015, g32p_row07_traceSegment_098_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_098 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 243 30 30, g32p_row07_traceSegment_098_0243_0030, g32p_row07_traceSegment_098_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 303 15 15, g32p_row07_traceSegment_098_0303_0015, g32p_row07_traceSegment_098_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 333 15 16, g32p_row07_traceSegment_098_0333_0015, g32p_row07_traceSegment_098_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 303 30 31, g32p_row07_traceSegment_098_0303_0030, g32p_row07_traceSegment_098_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_098 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 243 60 61, g32p_row07_traceSegment_098_0243_0060, g32p_row07_traceSegment_098_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 364 15 15, g32p_row07_traceSegment_098_0364_0015, g32p_row07_traceSegment_098_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 394 15 16, g32p_row07_traceSegment_098_0394_0015, g32p_row07_traceSegment_098_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 364 30 31, g32p_row07_traceSegment_098_0364_0030, g32p_row07_traceSegment_098_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 425 15 15, g32p_row07_traceSegment_098_0425_0015, g32p_row07_traceSegment_098_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 455 15 16, g32p_row07_traceSegment_098_0455_0015, g32p_row07_traceSegment_098_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 425 30 31, g32p_row07_traceSegment_098_0425_0030, g32p_row07_traceSegment_098_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_098 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 364 61 61, g32p_row07_traceSegment_098_0364_0061, g32p_row07_traceSegment_098_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_098 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 243 121 122, g32p_row07_traceSegment_098_0243_0121, g32p_row07_traceSegment_098_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_098 0 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 0 243 243, g32p_row07_traceSegment_098_0000_0243, g32p_row07_traceSegment_098_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 486 15 15, g32p_row07_traceSegment_098_0486_0015, g32p_row07_traceSegment_098_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 516 15 15, g32p_row07_traceSegment_098_0516_0015, g32p_row07_traceSegment_098_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_098 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 486 30 30, g32p_row07_traceSegment_098_0486_0030, g32p_row07_traceSegment_098_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 546 15 15, g32p_row07_traceSegment_098_0546_0015, g32p_row07_traceSegment_098_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 576 15 16, g32p_row07_traceSegment_098_0576_0015, g32p_row07_traceSegment_098_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 546 30 31, g32p_row07_traceSegment_098_0546_0030, g32p_row07_traceSegment_098_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_098 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 486 60 61, g32p_row07_traceSegment_098_0486_0060, g32p_row07_traceSegment_098_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 607 15 15, g32p_row07_traceSegment_098_0607_0015, g32p_row07_traceSegment_098_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 637 15 16, g32p_row07_traceSegment_098_0637_0015, g32p_row07_traceSegment_098_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 607 30 31, g32p_row07_traceSegment_098_0607_0030, g32p_row07_traceSegment_098_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 668 15 15, g32p_row07_traceSegment_098_0668_0015, g32p_row07_traceSegment_098_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 698 15 16, g32p_row07_traceSegment_098_0698_0015, g32p_row07_traceSegment_098_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 668 30 31, g32p_row07_traceSegment_098_0668_0030, g32p_row07_traceSegment_098_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_098 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 607 61 61, g32p_row07_traceSegment_098_0607_0061, g32p_row07_traceSegment_098_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_098 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 486 121 122, g32p_row07_traceSegment_098_0486_0121, g32p_row07_traceSegment_098_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 729 15 15, g32p_row07_traceSegment_098_0729_0015, g32p_row07_traceSegment_098_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 759 15 15, g32p_row07_traceSegment_098_0759_0015, g32p_row07_traceSegment_098_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_098 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 729 30 30, g32p_row07_traceSegment_098_0729_0030, g32p_row07_traceSegment_098_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 789 15 15, g32p_row07_traceSegment_098_0789_0015, g32p_row07_traceSegment_098_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 819 15 16, g32p_row07_traceSegment_098_0819_0015, g32p_row07_traceSegment_098_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 789 30 31, g32p_row07_traceSegment_098_0789_0030, g32p_row07_traceSegment_098_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_098 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 729 60 61, g32p_row07_traceSegment_098_0729_0060, g32p_row07_traceSegment_098_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 850 15 15, g32p_row07_traceSegment_098_0850_0015, g32p_row07_traceSegment_098_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 880 15 16, g32p_row07_traceSegment_098_0880_0015, g32p_row07_traceSegment_098_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 850 30 31, g32p_row07_traceSegment_098_0850_0030, g32p_row07_traceSegment_098_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 911 15 15, g32p_row07_traceSegment_098_0911_0015, g32p_row07_traceSegment_098_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 941 15 16, g32p_row07_traceSegment_098_0941_0015, g32p_row07_traceSegment_098_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 911 30 31, g32p_row07_traceSegment_098_0911_0030, g32p_row07_traceSegment_098_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_098 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 850 61 61, g32p_row07_traceSegment_098_0850_0061, g32p_row07_traceSegment_098_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_098 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 729 121 122, g32p_row07_traceSegment_098_0729_0121, g32p_row07_traceSegment_098_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_098 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 486 243 243, g32p_row07_traceSegment_098_0486_0243, g32p_row07_traceSegment_098_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_098 0 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 0 486 486, g32p_row07_traceSegment_098_0000_0486, g32p_row07_traceSegment_098_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 972 15 15, g32p_row07_traceSegment_098_0972_0015, g32p_row07_traceSegment_098_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1002 15 15, g32p_row07_traceSegment_098_1002_0015, g32p_row07_traceSegment_098_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_098 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 972 30 30, g32p_row07_traceSegment_098_0972_0030, g32p_row07_traceSegment_098_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1032 15 15, g32p_row07_traceSegment_098_1032_0015, g32p_row07_traceSegment_098_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1062 15 16, g32p_row07_traceSegment_098_1062_0015, g32p_row07_traceSegment_098_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1032 30 31, g32p_row07_traceSegment_098_1032_0030, g32p_row07_traceSegment_098_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_098 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 972 60 61, g32p_row07_traceSegment_098_0972_0060, g32p_row07_traceSegment_098_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1093 15 15, g32p_row07_traceSegment_098_1093_0015, g32p_row07_traceSegment_098_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1123 15 16, g32p_row07_traceSegment_098_1123_0015, g32p_row07_traceSegment_098_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1093 30 31, g32p_row07_traceSegment_098_1093_0030, g32p_row07_traceSegment_098_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1154 15 15, g32p_row07_traceSegment_098_1154_0015, g32p_row07_traceSegment_098_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1184 15 16, g32p_row07_traceSegment_098_1184_0015, g32p_row07_traceSegment_098_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1154 30 31, g32p_row07_traceSegment_098_1154_0030, g32p_row07_traceSegment_098_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_098 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1093 61 61, g32p_row07_traceSegment_098_1093_0061, g32p_row07_traceSegment_098_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_098 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 972 121 122, g32p_row07_traceSegment_098_0972_0121, g32p_row07_traceSegment_098_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1215 15 15, g32p_row07_traceSegment_098_1215_0015, g32p_row07_traceSegment_098_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1245 15 15, g32p_row07_traceSegment_098_1245_0015, g32p_row07_traceSegment_098_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_098 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1215 30 30, g32p_row07_traceSegment_098_1215_0030, g32p_row07_traceSegment_098_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1290 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1275 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1275 15 15, g32p_row07_traceSegment_098_1275_0015, g32p_row07_traceSegment_098_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1305 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1305 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1305 15 16, g32p_row07_traceSegment_098_1305_0015, g32p_row07_traceSegment_098_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1275 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1275 30 31, g32p_row07_traceSegment_098_1275_0030, g32p_row07_traceSegment_098_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_098 1215 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1215 60 61, g32p_row07_traceSegment_098_1215_0060, g32p_row07_traceSegment_098_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1336 15 15, g32p_row07_traceSegment_098_1336_0015, g32p_row07_traceSegment_098_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1366 15 16, g32p_row07_traceSegment_098_1366_0015, g32p_row07_traceSegment_098_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1336 30 31, g32p_row07_traceSegment_098_1336_0030, g32p_row07_traceSegment_098_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1397 15 15, g32p_row07_traceSegment_098_1397_0015, g32p_row07_traceSegment_098_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1427 15 16, g32p_row07_traceSegment_098_1427_0015, g32p_row07_traceSegment_098_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1397 30 31, g32p_row07_traceSegment_098_1397_0030, g32p_row07_traceSegment_098_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_098 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1336 61 61, g32p_row07_traceSegment_098_1336_0061, g32p_row07_traceSegment_098_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_098 1215 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1215 121 122, g32p_row07_traceSegment_098_1215_0121, g32p_row07_traceSegment_098_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_098 972 486 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 972 243 243, g32p_row07_traceSegment_098_0972_0243, g32p_row07_traceSegment_098_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1458 15 15, g32p_row07_traceSegment_098_1458_0015, g32p_row07_traceSegment_098_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1488 15 15, g32p_row07_traceSegment_098_1488_0015, g32p_row07_traceSegment_098_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_098 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1458 30 30, g32p_row07_traceSegment_098_1458_0030, g32p_row07_traceSegment_098_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1518 15 15, g32p_row07_traceSegment_098_1518_0015, g32p_row07_traceSegment_098_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1563 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1548 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1548 15 16, g32p_row07_traceSegment_098_1548_0015, g32p_row07_traceSegment_098_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1518 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1518 30 31, g32p_row07_traceSegment_098_1518_0030, g32p_row07_traceSegment_098_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_098 1458 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1458 60 61, g32p_row07_traceSegment_098_1458_0060, g32p_row07_traceSegment_098_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1579 15 15, g32p_row07_traceSegment_098_1579_0015, g32p_row07_traceSegment_098_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1609 15 16, g32p_row07_traceSegment_098_1609_0015, g32p_row07_traceSegment_098_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1579 30 31, g32p_row07_traceSegment_098_1579_0030, g32p_row07_traceSegment_098_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1640 15 15, g32p_row07_traceSegment_098_1640_0015, g32p_row07_traceSegment_098_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1670 15 16, g32p_row07_traceSegment_098_1670_0015, g32p_row07_traceSegment_098_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1640 30 31, g32p_row07_traceSegment_098_1640_0030, g32p_row07_traceSegment_098_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_098 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1579 61 61, g32p_row07_traceSegment_098_1579_0061, g32p_row07_traceSegment_098_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_098 1458 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1458 121 122, g32p_row07_traceSegment_098_1458_0121, g32p_row07_traceSegment_098_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1701 15 15, g32p_row07_traceSegment_098_1701_0015, g32p_row07_traceSegment_098_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1731 15 15, g32p_row07_traceSegment_098_1731_0015, g32p_row07_traceSegment_098_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_098 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1701 30 30, g32p_row07_traceSegment_098_1701_0030, g32p_row07_traceSegment_098_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1761 15 15, g32p_row07_traceSegment_098_1761_0015, g32p_row07_traceSegment_098_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1791 15 16, g32p_row07_traceSegment_098_1791_0015, g32p_row07_traceSegment_098_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1761 30 31, g32p_row07_traceSegment_098_1761_0030, g32p_row07_traceSegment_098_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_098 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1701 60 61, g32p_row07_traceSegment_098_1701_0060, g32p_row07_traceSegment_098_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1822 15 15, g32p_row07_traceSegment_098_1822_0015, g32p_row07_traceSegment_098_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1852 15 16, g32p_row07_traceSegment_098_1852_0015, g32p_row07_traceSegment_098_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1822 30 31, g32p_row07_traceSegment_098_1822_0030, g32p_row07_traceSegment_098_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_098 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1883 15 15, g32p_row07_traceSegment_098_1883_0015, g32p_row07_traceSegment_098_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_098 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_098 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_098_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_098 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1913 15 16, g32p_row07_traceSegment_098_1913_0015, g32p_row07_traceSegment_098_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_098 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1883 30 31, g32p_row07_traceSegment_098_1883_0030, g32p_row07_traceSegment_098_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_098 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1822 61 61, g32p_row07_traceSegment_098_1822_0061, g32p_row07_traceSegment_098_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_098 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1701 121 122, g32p_row07_traceSegment_098_1701_0121, g32p_row07_traceSegment_098_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_098_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_098 1458 486 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 1458 243 243, g32p_row07_traceSegment_098_1458_0243, g32p_row07_traceSegment_098_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_098 972 972 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 972 486 486, g32p_row07_traceSegment_098_0972_0486, g32p_row07_traceSegment_098_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_098_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_098 0 1944 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_098 0 972 972, g32p_row07_traceSegment_098_0000_0972, g32p_row07_traceSegment_098_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 98 = [0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_098_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_099_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 0 15 15, g32p_row07_traceSegment_099_0000_0015, g32p_row07_traceSegment_099_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 30 15 15, g32p_row07_traceSegment_099_0030_0015, g32p_row07_traceSegment_099_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_099 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 0 30 30, g32p_row07_traceSegment_099_0000_0030, g32p_row07_traceSegment_099_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 60 15 15, g32p_row07_traceSegment_099_0060_0015, g32p_row07_traceSegment_099_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 90 15 16, g32p_row07_traceSegment_099_0090_0015, g32p_row07_traceSegment_099_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 60 30 31, g32p_row07_traceSegment_099_0060_0030, g32p_row07_traceSegment_099_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_099 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 0 60 61, g32p_row07_traceSegment_099_0000_0060, g32p_row07_traceSegment_099_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 121 15 15, g32p_row07_traceSegment_099_0121_0015, g32p_row07_traceSegment_099_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 151 15 16, g32p_row07_traceSegment_099_0151_0015, g32p_row07_traceSegment_099_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 121 30 31, g32p_row07_traceSegment_099_0121_0030, g32p_row07_traceSegment_099_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 182 15 15, g32p_row07_traceSegment_099_0182_0015, g32p_row07_traceSegment_099_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 212 15 16, g32p_row07_traceSegment_099_0212_0015, g32p_row07_traceSegment_099_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 182 30 31, g32p_row07_traceSegment_099_0182_0030, g32p_row07_traceSegment_099_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_099 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 121 61 61, g32p_row07_traceSegment_099_0121_0061, g32p_row07_traceSegment_099_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_099 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 0 121 122, g32p_row07_traceSegment_099_0000_0121, g32p_row07_traceSegment_099_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 243 15 15, g32p_row07_traceSegment_099_0243_0015, g32p_row07_traceSegment_099_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 273 15 15, g32p_row07_traceSegment_099_0273_0015, g32p_row07_traceSegment_099_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_099 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 243 30 30, g32p_row07_traceSegment_099_0243_0030, g32p_row07_traceSegment_099_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 303 15 15, g32p_row07_traceSegment_099_0303_0015, g32p_row07_traceSegment_099_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 333 15 16, g32p_row07_traceSegment_099_0333_0015, g32p_row07_traceSegment_099_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 303 30 31, g32p_row07_traceSegment_099_0303_0030, g32p_row07_traceSegment_099_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_099 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 243 60 61, g32p_row07_traceSegment_099_0243_0060, g32p_row07_traceSegment_099_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 364 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 364 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 364 15 15, g32p_row07_traceSegment_099_0364_0015, g32p_row07_traceSegment_099_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 394 15 16, g32p_row07_traceSegment_099_0394_0015, g32p_row07_traceSegment_099_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 364 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 364 30 31, g32p_row07_traceSegment_099_0364_0030, g32p_row07_traceSegment_099_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 425 15 15, g32p_row07_traceSegment_099_0425_0015, g32p_row07_traceSegment_099_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 455 15 16, g32p_row07_traceSegment_099_0455_0015, g32p_row07_traceSegment_099_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 425 30 31, g32p_row07_traceSegment_099_0425_0030, g32p_row07_traceSegment_099_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_099 364 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 364 61 61, g32p_row07_traceSegment_099_0364_0061, g32p_row07_traceSegment_099_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_099 243 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 243 121 122, g32p_row07_traceSegment_099_0243_0121, g32p_row07_traceSegment_099_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_099 0 486 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 0 243 243, g32p_row07_traceSegment_099_0000_0243, g32p_row07_traceSegment_099_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 486 15 15, g32p_row07_traceSegment_099_0486_0015, g32p_row07_traceSegment_099_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 516 15 15, g32p_row07_traceSegment_099_0516_0015, g32p_row07_traceSegment_099_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_099 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 486 30 30, g32p_row07_traceSegment_099_0486_0030, g32p_row07_traceSegment_099_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 546 15 15, g32p_row07_traceSegment_099_0546_0015, g32p_row07_traceSegment_099_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 576 15 16, g32p_row07_traceSegment_099_0576_0015, g32p_row07_traceSegment_099_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 546 30 31, g32p_row07_traceSegment_099_0546_0030, g32p_row07_traceSegment_099_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_099 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 486 60 61, g32p_row07_traceSegment_099_0486_0060, g32p_row07_traceSegment_099_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 607 15 15, g32p_row07_traceSegment_099_0607_0015, g32p_row07_traceSegment_099_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 637 15 16, g32p_row07_traceSegment_099_0637_0015, g32p_row07_traceSegment_099_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 607 30 31, g32p_row07_traceSegment_099_0607_0030, g32p_row07_traceSegment_099_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 668 15 15, g32p_row07_traceSegment_099_0668_0015, g32p_row07_traceSegment_099_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 698 15 16, g32p_row07_traceSegment_099_0698_0015, g32p_row07_traceSegment_099_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 668 30 31, g32p_row07_traceSegment_099_0668_0030, g32p_row07_traceSegment_099_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_099 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 607 61 61, g32p_row07_traceSegment_099_0607_0061, g32p_row07_traceSegment_099_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_099 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 486 121 122, g32p_row07_traceSegment_099_0486_0121, g32p_row07_traceSegment_099_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 729 15 15, g32p_row07_traceSegment_099_0729_0015, g32p_row07_traceSegment_099_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 759 15 15, g32p_row07_traceSegment_099_0759_0015, g32p_row07_traceSegment_099_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_099 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 729 30 30, g32p_row07_traceSegment_099_0729_0030, g32p_row07_traceSegment_099_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 789 15 15, g32p_row07_traceSegment_099_0789_0015, g32p_row07_traceSegment_099_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 819 15 16, g32p_row07_traceSegment_099_0819_0015, g32p_row07_traceSegment_099_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 789 30 31, g32p_row07_traceSegment_099_0789_0030, g32p_row07_traceSegment_099_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_099 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 729 60 61, g32p_row07_traceSegment_099_0729_0060, g32p_row07_traceSegment_099_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 850 15 15, g32p_row07_traceSegment_099_0850_0015, g32p_row07_traceSegment_099_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 880 15 16, g32p_row07_traceSegment_099_0880_0015, g32p_row07_traceSegment_099_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 850 30 31, g32p_row07_traceSegment_099_0850_0030, g32p_row07_traceSegment_099_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 911 15 15, g32p_row07_traceSegment_099_0911_0015, g32p_row07_traceSegment_099_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 941 15 16, g32p_row07_traceSegment_099_0941_0015, g32p_row07_traceSegment_099_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 911 30 31, g32p_row07_traceSegment_099_0911_0030, g32p_row07_traceSegment_099_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_099 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 850 61 61, g32p_row07_traceSegment_099_0850_0061, g32p_row07_traceSegment_099_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_099 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 729 121 122, g32p_row07_traceSegment_099_0729_0121, g32p_row07_traceSegment_099_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_099 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 486 243 243, g32p_row07_traceSegment_099_0486_0243, g32p_row07_traceSegment_099_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_099 0 972 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 0 486 486, g32p_row07_traceSegment_099_0000_0486, g32p_row07_traceSegment_099_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 972 15 15, g32p_row07_traceSegment_099_0972_0015, g32p_row07_traceSegment_099_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1002 15 15, g32p_row07_traceSegment_099_1002_0015, g32p_row07_traceSegment_099_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_099 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 972 30 30, g32p_row07_traceSegment_099_0972_0030, g32p_row07_traceSegment_099_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1032 15 15, g32p_row07_traceSegment_099_1032_0015, g32p_row07_traceSegment_099_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1062 15 16, g32p_row07_traceSegment_099_1062_0015, g32p_row07_traceSegment_099_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1032 30 31, g32p_row07_traceSegment_099_1032_0030, g32p_row07_traceSegment_099_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_099 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 972 60 61, g32p_row07_traceSegment_099_0972_0060, g32p_row07_traceSegment_099_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1093 15 15, g32p_row07_traceSegment_099_1093_0015, g32p_row07_traceSegment_099_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1123 15 16, g32p_row07_traceSegment_099_1123_0015, g32p_row07_traceSegment_099_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1093 30 31, g32p_row07_traceSegment_099_1093_0030, g32p_row07_traceSegment_099_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1154 15 15, g32p_row07_traceSegment_099_1154_0015, g32p_row07_traceSegment_099_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1184 15 16, g32p_row07_traceSegment_099_1184_0015, g32p_row07_traceSegment_099_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1154 30 31, g32p_row07_traceSegment_099_1154_0030, g32p_row07_traceSegment_099_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_099 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1093 61 61, g32p_row07_traceSegment_099_1093_0061, g32p_row07_traceSegment_099_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_099 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 972 121 122, g32p_row07_traceSegment_099_0972_0121, g32p_row07_traceSegment_099_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1215 15 15, g32p_row07_traceSegment_099_1215_0015, g32p_row07_traceSegment_099_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1245 15 15, g32p_row07_traceSegment_099_1245_0015, g32p_row07_traceSegment_099_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_099 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1215 30 30, g32p_row07_traceSegment_099_1215_0030, g32p_row07_traceSegment_099_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1275 15 15, g32p_row07_traceSegment_099_1275_0015, g32p_row07_traceSegment_099_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1305 15 16, g32p_row07_traceSegment_099_1305_0015, g32p_row07_traceSegment_099_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1275 30 31, g32p_row07_traceSegment_099_1275_0030, g32p_row07_traceSegment_099_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_099 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1215 60 61, g32p_row07_traceSegment_099_1215_0060, g32p_row07_traceSegment_099_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1336 15 15, g32p_row07_traceSegment_099_1336_0015, g32p_row07_traceSegment_099_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1366 15 16, g32p_row07_traceSegment_099_1366_0015, g32p_row07_traceSegment_099_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1336 30 31, g32p_row07_traceSegment_099_1336_0030, g32p_row07_traceSegment_099_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1397 15 15, g32p_row07_traceSegment_099_1397_0015, g32p_row07_traceSegment_099_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1427 15 16, g32p_row07_traceSegment_099_1427_0015, g32p_row07_traceSegment_099_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1397 30 31, g32p_row07_traceSegment_099_1397_0030, g32p_row07_traceSegment_099_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_099 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1336 61 61, g32p_row07_traceSegment_099_1336_0061, g32p_row07_traceSegment_099_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_099 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1215 121 122, g32p_row07_traceSegment_099_1215_0121, g32p_row07_traceSegment_099_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_099 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 972 243 243, g32p_row07_traceSegment_099_0972_0243, g32p_row07_traceSegment_099_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1458 15 15, g32p_row07_traceSegment_099_1458_0015, g32p_row07_traceSegment_099_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1488 15 15, g32p_row07_traceSegment_099_1488_0015, g32p_row07_traceSegment_099_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_099 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1458 30 30, g32p_row07_traceSegment_099_1458_0030, g32p_row07_traceSegment_099_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1518 15 15, g32p_row07_traceSegment_099_1518_0015, g32p_row07_traceSegment_099_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1548 15 16, g32p_row07_traceSegment_099_1548_0015, g32p_row07_traceSegment_099_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1518 30 31, g32p_row07_traceSegment_099_1518_0030, g32p_row07_traceSegment_099_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_099 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1458 60 61, g32p_row07_traceSegment_099_1458_0060, g32p_row07_traceSegment_099_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1579 15 15, g32p_row07_traceSegment_099_1579_0015, g32p_row07_traceSegment_099_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1609 15 16, g32p_row07_traceSegment_099_1609_0015, g32p_row07_traceSegment_099_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1579 30 31, g32p_row07_traceSegment_099_1579_0030, g32p_row07_traceSegment_099_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1640 15 15, g32p_row07_traceSegment_099_1640_0015, g32p_row07_traceSegment_099_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1670 15 16, g32p_row07_traceSegment_099_1670_0015, g32p_row07_traceSegment_099_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1640 30 31, g32p_row07_traceSegment_099_1640_0030, g32p_row07_traceSegment_099_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_099 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1579 61 61, g32p_row07_traceSegment_099_1579_0061, g32p_row07_traceSegment_099_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_099 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1458 121 122, g32p_row07_traceSegment_099_1458_0121, g32p_row07_traceSegment_099_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1701 15 15, g32p_row07_traceSegment_099_1701_0015, g32p_row07_traceSegment_099_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1731 15 15, g32p_row07_traceSegment_099_1731_0015, g32p_row07_traceSegment_099_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_099 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1701 30 30, g32p_row07_traceSegment_099_1701_0030, g32p_row07_traceSegment_099_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1761 15 15, g32p_row07_traceSegment_099_1761_0015, g32p_row07_traceSegment_099_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1791 15 16, g32p_row07_traceSegment_099_1791_0015, g32p_row07_traceSegment_099_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1761 30 31, g32p_row07_traceSegment_099_1761_0030, g32p_row07_traceSegment_099_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_099 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1701 60 61, g32p_row07_traceSegment_099_1701_0060, g32p_row07_traceSegment_099_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1822 15 15, g32p_row07_traceSegment_099_1822_0015, g32p_row07_traceSegment_099_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1852 15 16, g32p_row07_traceSegment_099_1852_0015, g32p_row07_traceSegment_099_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1822 30 31, g32p_row07_traceSegment_099_1822_0030, g32p_row07_traceSegment_099_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_099 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1883 15 15, g32p_row07_traceSegment_099_1883_0015, g32p_row07_traceSegment_099_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_099 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_099 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_099_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_099 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1913 15 16, g32p_row07_traceSegment_099_1913_0015, g32p_row07_traceSegment_099_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_099 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1883 30 31, g32p_row07_traceSegment_099_1883_0030, g32p_row07_traceSegment_099_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_099 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1822 61 61, g32p_row07_traceSegment_099_1822_0061, g32p_row07_traceSegment_099_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_099 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1701 121 122, g32p_row07_traceSegment_099_1701_0121, g32p_row07_traceSegment_099_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_099_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_099 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 1458 243 243, g32p_row07_traceSegment_099_1458_0243, g32p_row07_traceSegment_099_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_099 972 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 972 486 486, g32p_row07_traceSegment_099_0972_0486, g32p_row07_traceSegment_099_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_099_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_099 0 1944 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_099 0 972 972, g32p_row07_traceSegment_099_0000_0972, g32p_row07_traceSegment_099_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_099_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_100 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 100 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_100_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 0 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 0 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 0 15 15, g32p_row07_traceSegment_100_0000_0015, g32p_row07_traceSegment_100_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 30 15 15, g32p_row07_traceSegment_100_0030_0015, g32p_row07_traceSegment_100_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_100 0 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 0 30 30, g32p_row07_traceSegment_100_0000_0030, g32p_row07_traceSegment_100_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 60 15 15, g32p_row07_traceSegment_100_0060_0015, g32p_row07_traceSegment_100_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 90 15 16, g32p_row07_traceSegment_100_0090_0015, g32p_row07_traceSegment_100_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 60 30 31, g32p_row07_traceSegment_100_0060_0030, g32p_row07_traceSegment_100_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_100 0 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 0 60 61, g32p_row07_traceSegment_100_0000_0060, g32p_row07_traceSegment_100_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 121 15 15, g32p_row07_traceSegment_100_0121_0015, g32p_row07_traceSegment_100_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 151 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 151 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 151 15 16, g32p_row07_traceSegment_100_0151_0015, g32p_row07_traceSegment_100_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 121 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 121 30 31, g32p_row07_traceSegment_100_0121_0030, g32p_row07_traceSegment_100_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 182 15 15, g32p_row07_traceSegment_100_0182_0015, g32p_row07_traceSegment_100_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 212 15 16, g32p_row07_traceSegment_100_0212_0015, g32p_row07_traceSegment_100_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 182 30 31, g32p_row07_traceSegment_100_0182_0030, g32p_row07_traceSegment_100_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_100 121 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 121 61 61, g32p_row07_traceSegment_100_0121_0061, g32p_row07_traceSegment_100_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_100 0 243 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 0 121 122, g32p_row07_traceSegment_100_0000_0121, g32p_row07_traceSegment_100_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 243 15 15, g32p_row07_traceSegment_100_0243_0015, g32p_row07_traceSegment_100_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 273 15 15, g32p_row07_traceSegment_100_0273_0015, g32p_row07_traceSegment_100_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_100 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 243 30 30, g32p_row07_traceSegment_100_0243_0030, g32p_row07_traceSegment_100_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 303 15 15, g32p_row07_traceSegment_100_0303_0015, g32p_row07_traceSegment_100_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 348 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 333 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 333 15 16, g32p_row07_traceSegment_100_0333_0015, g32p_row07_traceSegment_100_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 303 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 303 30 31, g32p_row07_traceSegment_100_0303_0030, g32p_row07_traceSegment_100_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_100 243 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 243 60 61, g32p_row07_traceSegment_100_0243_0060, g32p_row07_traceSegment_100_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 364 15 15, g32p_row07_traceSegment_100_0364_0015, g32p_row07_traceSegment_100_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 394 15 16, g32p_row07_traceSegment_100_0394_0015, g32p_row07_traceSegment_100_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 364 30 31, g32p_row07_traceSegment_100_0364_0030, g32p_row07_traceSegment_100_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 425 15 15, g32p_row07_traceSegment_100_0425_0015, g32p_row07_traceSegment_100_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 455 15 16, g32p_row07_traceSegment_100_0455_0015, g32p_row07_traceSegment_100_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 425 30 31, g32p_row07_traceSegment_100_0425_0030, g32p_row07_traceSegment_100_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_100 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 364 61 61, g32p_row07_traceSegment_100_0364_0061, g32p_row07_traceSegment_100_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_100 243 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 243 121 122, g32p_row07_traceSegment_100_0243_0121, g32p_row07_traceSegment_100_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_100 0 486 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 0 243 243, g32p_row07_traceSegment_100_0000_0243, g32p_row07_traceSegment_100_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 486 15 15, g32p_row07_traceSegment_100_0486_0015, g32p_row07_traceSegment_100_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 516 15 15, g32p_row07_traceSegment_100_0516_0015, g32p_row07_traceSegment_100_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_100 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 486 30 30, g32p_row07_traceSegment_100_0486_0030, g32p_row07_traceSegment_100_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 546 15 15, g32p_row07_traceSegment_100_0546_0015, g32p_row07_traceSegment_100_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 576 15 16, g32p_row07_traceSegment_100_0576_0015, g32p_row07_traceSegment_100_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 546 30 31, g32p_row07_traceSegment_100_0546_0030, g32p_row07_traceSegment_100_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_100 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 486 60 61, g32p_row07_traceSegment_100_0486_0060, g32p_row07_traceSegment_100_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 607 15 15, g32p_row07_traceSegment_100_0607_0015, g32p_row07_traceSegment_100_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 637 15 16, g32p_row07_traceSegment_100_0637_0015, g32p_row07_traceSegment_100_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 607 30 31, g32p_row07_traceSegment_100_0607_0030, g32p_row07_traceSegment_100_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 668 15 15, g32p_row07_traceSegment_100_0668_0015, g32p_row07_traceSegment_100_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 698 15 16, g32p_row07_traceSegment_100_0698_0015, g32p_row07_traceSegment_100_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 668 30 31, g32p_row07_traceSegment_100_0668_0030, g32p_row07_traceSegment_100_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_100 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 607 61 61, g32p_row07_traceSegment_100_0607_0061, g32p_row07_traceSegment_100_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_100 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 486 121 122, g32p_row07_traceSegment_100_0486_0121, g32p_row07_traceSegment_100_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 729 15 15, g32p_row07_traceSegment_100_0729_0015, g32p_row07_traceSegment_100_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 759 15 15, g32p_row07_traceSegment_100_0759_0015, g32p_row07_traceSegment_100_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_100 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 729 30 30, g32p_row07_traceSegment_100_0729_0030, g32p_row07_traceSegment_100_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 789 15 15, g32p_row07_traceSegment_100_0789_0015, g32p_row07_traceSegment_100_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 819 15 16, g32p_row07_traceSegment_100_0819_0015, g32p_row07_traceSegment_100_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 789 30 31, g32p_row07_traceSegment_100_0789_0030, g32p_row07_traceSegment_100_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_100 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 729 60 61, g32p_row07_traceSegment_100_0729_0060, g32p_row07_traceSegment_100_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 850 15 15, g32p_row07_traceSegment_100_0850_0015, g32p_row07_traceSegment_100_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 880 15 16, g32p_row07_traceSegment_100_0880_0015, g32p_row07_traceSegment_100_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 850 30 31, g32p_row07_traceSegment_100_0850_0030, g32p_row07_traceSegment_100_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 911 15 15, g32p_row07_traceSegment_100_0911_0015, g32p_row07_traceSegment_100_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 941 15 16, g32p_row07_traceSegment_100_0941_0015, g32p_row07_traceSegment_100_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 911 30 31, g32p_row07_traceSegment_100_0911_0030, g32p_row07_traceSegment_100_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_100 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 850 61 61, g32p_row07_traceSegment_100_0850_0061, g32p_row07_traceSegment_100_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_100 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 729 121 122, g32p_row07_traceSegment_100_0729_0121, g32p_row07_traceSegment_100_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_100 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 486 243 243, g32p_row07_traceSegment_100_0486_0243, g32p_row07_traceSegment_100_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_100 0 972 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 0 486 486, g32p_row07_traceSegment_100_0000_0486, g32p_row07_traceSegment_100_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 972 15 15, g32p_row07_traceSegment_100_0972_0015, g32p_row07_traceSegment_100_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1002 15 15, g32p_row07_traceSegment_100_1002_0015, g32p_row07_traceSegment_100_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_100 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 972 30 30, g32p_row07_traceSegment_100_0972_0030, g32p_row07_traceSegment_100_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1032 15 15, g32p_row07_traceSegment_100_1032_0015, g32p_row07_traceSegment_100_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1062 15 16, g32p_row07_traceSegment_100_1062_0015, g32p_row07_traceSegment_100_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1032 30 31, g32p_row07_traceSegment_100_1032_0030, g32p_row07_traceSegment_100_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_100 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 972 60 61, g32p_row07_traceSegment_100_0972_0060, g32p_row07_traceSegment_100_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1093 15 15, g32p_row07_traceSegment_100_1093_0015, g32p_row07_traceSegment_100_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1123 15 16, g32p_row07_traceSegment_100_1123_0015, g32p_row07_traceSegment_100_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1093 30 31, g32p_row07_traceSegment_100_1093_0030, g32p_row07_traceSegment_100_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1154 15 15, g32p_row07_traceSegment_100_1154_0015, g32p_row07_traceSegment_100_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1184 15 16, g32p_row07_traceSegment_100_1184_0015, g32p_row07_traceSegment_100_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1154 30 31, g32p_row07_traceSegment_100_1154_0030, g32p_row07_traceSegment_100_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_100 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1093 61 61, g32p_row07_traceSegment_100_1093_0061, g32p_row07_traceSegment_100_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_100 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 972 121 122, g32p_row07_traceSegment_100_0972_0121, g32p_row07_traceSegment_100_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1215 15 15, g32p_row07_traceSegment_100_1215_0015, g32p_row07_traceSegment_100_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1245 15 15, g32p_row07_traceSegment_100_1245_0015, g32p_row07_traceSegment_100_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_100 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1215 30 30, g32p_row07_traceSegment_100_1215_0030, g32p_row07_traceSegment_100_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1275 15 15, g32p_row07_traceSegment_100_1275_0015, g32p_row07_traceSegment_100_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1305 15 16, g32p_row07_traceSegment_100_1305_0015, g32p_row07_traceSegment_100_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1275 30 31, g32p_row07_traceSegment_100_1275_0030, g32p_row07_traceSegment_100_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_100 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1215 60 61, g32p_row07_traceSegment_100_1215_0060, g32p_row07_traceSegment_100_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1336 15 15, g32p_row07_traceSegment_100_1336_0015, g32p_row07_traceSegment_100_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1366 15 16, g32p_row07_traceSegment_100_1366_0015, g32p_row07_traceSegment_100_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1336 30 31, g32p_row07_traceSegment_100_1336_0030, g32p_row07_traceSegment_100_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1397 15 15, g32p_row07_traceSegment_100_1397_0015, g32p_row07_traceSegment_100_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1427 15 16, g32p_row07_traceSegment_100_1427_0015, g32p_row07_traceSegment_100_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1397 30 31, g32p_row07_traceSegment_100_1397_0030, g32p_row07_traceSegment_100_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_100 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1336 61 61, g32p_row07_traceSegment_100_1336_0061, g32p_row07_traceSegment_100_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_100 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1215 121 122, g32p_row07_traceSegment_100_1215_0121, g32p_row07_traceSegment_100_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_100 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 972 243 243, g32p_row07_traceSegment_100_0972_0243, g32p_row07_traceSegment_100_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1458 15 15, g32p_row07_traceSegment_100_1458_0015, g32p_row07_traceSegment_100_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1488 15 15, g32p_row07_traceSegment_100_1488_0015, g32p_row07_traceSegment_100_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_100 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1458 30 30, g32p_row07_traceSegment_100_1458_0030, g32p_row07_traceSegment_100_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1518 15 15, g32p_row07_traceSegment_100_1518_0015, g32p_row07_traceSegment_100_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1548 15 16, g32p_row07_traceSegment_100_1548_0015, g32p_row07_traceSegment_100_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1518 30 31, g32p_row07_traceSegment_100_1518_0030, g32p_row07_traceSegment_100_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_100 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1458 60 61, g32p_row07_traceSegment_100_1458_0060, g32p_row07_traceSegment_100_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1579 15 15, g32p_row07_traceSegment_100_1579_0015, g32p_row07_traceSegment_100_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1609 15 16, g32p_row07_traceSegment_100_1609_0015, g32p_row07_traceSegment_100_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1579 30 31, g32p_row07_traceSegment_100_1579_0030, g32p_row07_traceSegment_100_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1640 15 15, g32p_row07_traceSegment_100_1640_0015, g32p_row07_traceSegment_100_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1670 15 16, g32p_row07_traceSegment_100_1670_0015, g32p_row07_traceSegment_100_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1640 30 31, g32p_row07_traceSegment_100_1640_0030, g32p_row07_traceSegment_100_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_100 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1579 61 61, g32p_row07_traceSegment_100_1579_0061, g32p_row07_traceSegment_100_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_100 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1458 121 122, g32p_row07_traceSegment_100_1458_0121, g32p_row07_traceSegment_100_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1701 15 15, g32p_row07_traceSegment_100_1701_0015, g32p_row07_traceSegment_100_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1731 15 15, g32p_row07_traceSegment_100_1731_0015, g32p_row07_traceSegment_100_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_100 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1701 30 30, g32p_row07_traceSegment_100_1701_0030, g32p_row07_traceSegment_100_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1761 15 15, g32p_row07_traceSegment_100_1761_0015, g32p_row07_traceSegment_100_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1791 15 16, g32p_row07_traceSegment_100_1791_0015, g32p_row07_traceSegment_100_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1761 30 31, g32p_row07_traceSegment_100_1761_0030, g32p_row07_traceSegment_100_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_100 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1701 60 61, g32p_row07_traceSegment_100_1701_0060, g32p_row07_traceSegment_100_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1822 15 15, g32p_row07_traceSegment_100_1822_0015, g32p_row07_traceSegment_100_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1852 15 16, g32p_row07_traceSegment_100_1852_0015, g32p_row07_traceSegment_100_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1822 30 31, g32p_row07_traceSegment_100_1822_0030, g32p_row07_traceSegment_100_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_100 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1883 15 15, g32p_row07_traceSegment_100_1883_0015, g32p_row07_traceSegment_100_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_100 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_100 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_100_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_100 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1913 15 16, g32p_row07_traceSegment_100_1913_0015, g32p_row07_traceSegment_100_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_100 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1883 30 31, g32p_row07_traceSegment_100_1883_0030, g32p_row07_traceSegment_100_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_100 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1822 61 61, g32p_row07_traceSegment_100_1822_0061, g32p_row07_traceSegment_100_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_100 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1701 121 122, g32p_row07_traceSegment_100_1701_0121, g32p_row07_traceSegment_100_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_100_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_100 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 1458 243 243, g32p_row07_traceSegment_100_1458_0243, g32p_row07_traceSegment_100_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_100 972 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 972 486 486, g32p_row07_traceSegment_100_0972_0486, g32p_row07_traceSegment_100_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_100_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_100 0 1944 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_100 0 972 972, g32p_row07_traceSegment_100_0000_0972, g32p_row07_traceSegment_100_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 100 = [0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_100_0000_1944

end HodgeLean.Foundations.Program

end
end
