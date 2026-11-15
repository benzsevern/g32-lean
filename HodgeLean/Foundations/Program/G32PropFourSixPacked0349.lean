import HodgeLean.Foundations.Program.G32PropFourSixPacked0347
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0348

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_024 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 24 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_024_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 0 15 15, g32p_row07_traceSegment_024_0000_0015, g32p_row07_traceSegment_024_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 30 15 15, g32p_row07_traceSegment_024_0030_0015, g32p_row07_traceSegment_024_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_024 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 0 30 30, g32p_row07_traceSegment_024_0000_0030, g32p_row07_traceSegment_024_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 60 15 15, g32p_row07_traceSegment_024_0060_0015, g32p_row07_traceSegment_024_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 90 15 16, g32p_row07_traceSegment_024_0090_0015, g32p_row07_traceSegment_024_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 60 30 31, g32p_row07_traceSegment_024_0060_0030, g32p_row07_traceSegment_024_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_024 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 0 60 61, g32p_row07_traceSegment_024_0000_0060, g32p_row07_traceSegment_024_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 121 15 15, g32p_row07_traceSegment_024_0121_0015, g32p_row07_traceSegment_024_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 151 15 16, g32p_row07_traceSegment_024_0151_0015, g32p_row07_traceSegment_024_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 121 30 31, g32p_row07_traceSegment_024_0121_0030, g32p_row07_traceSegment_024_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 182 15 15, g32p_row07_traceSegment_024_0182_0015, g32p_row07_traceSegment_024_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 212 15 16, g32p_row07_traceSegment_024_0212_0015, g32p_row07_traceSegment_024_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 182 30 31, g32p_row07_traceSegment_024_0182_0030, g32p_row07_traceSegment_024_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_024 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 121 61 61, g32p_row07_traceSegment_024_0121_0061, g32p_row07_traceSegment_024_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_024 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 0 121 122, g32p_row07_traceSegment_024_0000_0121, g32p_row07_traceSegment_024_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 243 15 15, g32p_row07_traceSegment_024_0243_0015, g32p_row07_traceSegment_024_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 273 15 15, g32p_row07_traceSegment_024_0273_0015, g32p_row07_traceSegment_024_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_024 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 243 30 30, g32p_row07_traceSegment_024_0243_0030, g32p_row07_traceSegment_024_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 303 15 15, g32p_row07_traceSegment_024_0303_0015, g32p_row07_traceSegment_024_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 333 15 16, g32p_row07_traceSegment_024_0333_0015, g32p_row07_traceSegment_024_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 303 30 31, g32p_row07_traceSegment_024_0303_0030, g32p_row07_traceSegment_024_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_024 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 243 60 61, g32p_row07_traceSegment_024_0243_0060, g32p_row07_traceSegment_024_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 364 15 15, g32p_row07_traceSegment_024_0364_0015, g32p_row07_traceSegment_024_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 394 15 16, g32p_row07_traceSegment_024_0394_0015, g32p_row07_traceSegment_024_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 364 30 31, g32p_row07_traceSegment_024_0364_0030, g32p_row07_traceSegment_024_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 425 15 15, g32p_row07_traceSegment_024_0425_0015, g32p_row07_traceSegment_024_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 470 16 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 455 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 455 15 16, g32p_row07_traceSegment_024_0455_0015, g32p_row07_traceSegment_024_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 425 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 425 30 31, g32p_row07_traceSegment_024_0425_0030, g32p_row07_traceSegment_024_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_024 364 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 364 61 61, g32p_row07_traceSegment_024_0364_0061, g32p_row07_traceSegment_024_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_024 243 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 243 121 122, g32p_row07_traceSegment_024_0243_0121, g32p_row07_traceSegment_024_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_024 0 486 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 0 243 243, g32p_row07_traceSegment_024_0000_0243, g32p_row07_traceSegment_024_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 486 15 15, g32p_row07_traceSegment_024_0486_0015, g32p_row07_traceSegment_024_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 516 15 15, g32p_row07_traceSegment_024_0516_0015, g32p_row07_traceSegment_024_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_024 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 486 30 30, g32p_row07_traceSegment_024_0486_0030, g32p_row07_traceSegment_024_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 546 15 15, g32p_row07_traceSegment_024_0546_0015, g32p_row07_traceSegment_024_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 576 15 16, g32p_row07_traceSegment_024_0576_0015, g32p_row07_traceSegment_024_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 546 30 31, g32p_row07_traceSegment_024_0546_0030, g32p_row07_traceSegment_024_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_024 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 486 60 61, g32p_row07_traceSegment_024_0486_0060, g32p_row07_traceSegment_024_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 607 15 15, g32p_row07_traceSegment_024_0607_0015, g32p_row07_traceSegment_024_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 637 15 16, g32p_row07_traceSegment_024_0637_0015, g32p_row07_traceSegment_024_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 607 30 31, g32p_row07_traceSegment_024_0607_0030, g32p_row07_traceSegment_024_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 668 15 15, g32p_row07_traceSegment_024_0668_0015, g32p_row07_traceSegment_024_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 698 15 16, g32p_row07_traceSegment_024_0698_0015, g32p_row07_traceSegment_024_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 668 30 31, g32p_row07_traceSegment_024_0668_0030, g32p_row07_traceSegment_024_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_024 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 607 61 61, g32p_row07_traceSegment_024_0607_0061, g32p_row07_traceSegment_024_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_024 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 486 121 122, g32p_row07_traceSegment_024_0486_0121, g32p_row07_traceSegment_024_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 729 15 15, g32p_row07_traceSegment_024_0729_0015, g32p_row07_traceSegment_024_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 759 15 15, g32p_row07_traceSegment_024_0759_0015, g32p_row07_traceSegment_024_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_024 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 729 30 30, g32p_row07_traceSegment_024_0729_0030, g32p_row07_traceSegment_024_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 789 15 15, g32p_row07_traceSegment_024_0789_0015, g32p_row07_traceSegment_024_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 819 15 16, g32p_row07_traceSegment_024_0819_0015, g32p_row07_traceSegment_024_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 789 30 31, g32p_row07_traceSegment_024_0789_0030, g32p_row07_traceSegment_024_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_024 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 729 60 61, g32p_row07_traceSegment_024_0729_0060, g32p_row07_traceSegment_024_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 850 15 15, g32p_row07_traceSegment_024_0850_0015, g32p_row07_traceSegment_024_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 880 15 16, g32p_row07_traceSegment_024_0880_0015, g32p_row07_traceSegment_024_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 850 30 31, g32p_row07_traceSegment_024_0850_0030, g32p_row07_traceSegment_024_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 911 15 15, g32p_row07_traceSegment_024_0911_0015, g32p_row07_traceSegment_024_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 941 15 16, g32p_row07_traceSegment_024_0941_0015, g32p_row07_traceSegment_024_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 911 30 31, g32p_row07_traceSegment_024_0911_0030, g32p_row07_traceSegment_024_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_024 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 850 61 61, g32p_row07_traceSegment_024_0850_0061, g32p_row07_traceSegment_024_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_024 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 729 121 122, g32p_row07_traceSegment_024_0729_0121, g32p_row07_traceSegment_024_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_024 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 486 243 243, g32p_row07_traceSegment_024_0486_0243, g32p_row07_traceSegment_024_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_024 0 972 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 0 486 486, g32p_row07_traceSegment_024_0000_0486, g32p_row07_traceSegment_024_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 972 15 15, g32p_row07_traceSegment_024_0972_0015, g32p_row07_traceSegment_024_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1002 15 15, g32p_row07_traceSegment_024_1002_0015, g32p_row07_traceSegment_024_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_024 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 972 30 30, g32p_row07_traceSegment_024_0972_0030, g32p_row07_traceSegment_024_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1032 15 15, g32p_row07_traceSegment_024_1032_0015, g32p_row07_traceSegment_024_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1062 15 16, g32p_row07_traceSegment_024_1062_0015, g32p_row07_traceSegment_024_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1032 30 31, g32p_row07_traceSegment_024_1032_0030, g32p_row07_traceSegment_024_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_024 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 972 60 61, g32p_row07_traceSegment_024_0972_0060, g32p_row07_traceSegment_024_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1093 15 15, g32p_row07_traceSegment_024_1093_0015, g32p_row07_traceSegment_024_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1123 15 16, g32p_row07_traceSegment_024_1123_0015, g32p_row07_traceSegment_024_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1093 30 31, g32p_row07_traceSegment_024_1093_0030, g32p_row07_traceSegment_024_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1154 15 15, g32p_row07_traceSegment_024_1154_0015, g32p_row07_traceSegment_024_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1184 15 16, g32p_row07_traceSegment_024_1184_0015, g32p_row07_traceSegment_024_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1154 30 31, g32p_row07_traceSegment_024_1154_0030, g32p_row07_traceSegment_024_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_024 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1093 61 61, g32p_row07_traceSegment_024_1093_0061, g32p_row07_traceSegment_024_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_024 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 972 121 122, g32p_row07_traceSegment_024_0972_0121, g32p_row07_traceSegment_024_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1215 15 15, g32p_row07_traceSegment_024_1215_0015, g32p_row07_traceSegment_024_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1245 15 15, g32p_row07_traceSegment_024_1245_0015, g32p_row07_traceSegment_024_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_024 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1215 30 30, g32p_row07_traceSegment_024_1215_0030, g32p_row07_traceSegment_024_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1275 15 15, g32p_row07_traceSegment_024_1275_0015, g32p_row07_traceSegment_024_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1305 15 16, g32p_row07_traceSegment_024_1305_0015, g32p_row07_traceSegment_024_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1275 30 31, g32p_row07_traceSegment_024_1275_0030, g32p_row07_traceSegment_024_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_024 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1215 60 61, g32p_row07_traceSegment_024_1215_0060, g32p_row07_traceSegment_024_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1336 15 15, g32p_row07_traceSegment_024_1336_0015, g32p_row07_traceSegment_024_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1366 15 16, g32p_row07_traceSegment_024_1366_0015, g32p_row07_traceSegment_024_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1336 30 31, g32p_row07_traceSegment_024_1336_0030, g32p_row07_traceSegment_024_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1397 15 15, g32p_row07_traceSegment_024_1397_0015, g32p_row07_traceSegment_024_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1427 15 16, g32p_row07_traceSegment_024_1427_0015, g32p_row07_traceSegment_024_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1397 30 31, g32p_row07_traceSegment_024_1397_0030, g32p_row07_traceSegment_024_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_024 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1336 61 61, g32p_row07_traceSegment_024_1336_0061, g32p_row07_traceSegment_024_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_024 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1215 121 122, g32p_row07_traceSegment_024_1215_0121, g32p_row07_traceSegment_024_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_024 972 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 972 243 243, g32p_row07_traceSegment_024_0972_0243, g32p_row07_traceSegment_024_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1458 15 15, g32p_row07_traceSegment_024_1458_0015, g32p_row07_traceSegment_024_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1488 15 15, g32p_row07_traceSegment_024_1488_0015, g32p_row07_traceSegment_024_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_024 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1458 30 30, g32p_row07_traceSegment_024_1458_0030, g32p_row07_traceSegment_024_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1518 15 15, g32p_row07_traceSegment_024_1518_0015, g32p_row07_traceSegment_024_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1548 15 16, g32p_row07_traceSegment_024_1548_0015, g32p_row07_traceSegment_024_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1518 30 31, g32p_row07_traceSegment_024_1518_0030, g32p_row07_traceSegment_024_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_024 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1458 60 61, g32p_row07_traceSegment_024_1458_0060, g32p_row07_traceSegment_024_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1579 15 15, g32p_row07_traceSegment_024_1579_0015, g32p_row07_traceSegment_024_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1609 15 16, g32p_row07_traceSegment_024_1609_0015, g32p_row07_traceSegment_024_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1579 30 31, g32p_row07_traceSegment_024_1579_0030, g32p_row07_traceSegment_024_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1640 15 15, g32p_row07_traceSegment_024_1640_0015, g32p_row07_traceSegment_024_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1670 15 16, g32p_row07_traceSegment_024_1670_0015, g32p_row07_traceSegment_024_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1640 30 31, g32p_row07_traceSegment_024_1640_0030, g32p_row07_traceSegment_024_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_024 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1579 61 61, g32p_row07_traceSegment_024_1579_0061, g32p_row07_traceSegment_024_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_024 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1458 121 122, g32p_row07_traceSegment_024_1458_0121, g32p_row07_traceSegment_024_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1701 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1716 15 = [3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1701 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1701 15 15, g32p_row07_traceSegment_024_1701_0015, g32p_row07_traceSegment_024_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1731 15 15, g32p_row07_traceSegment_024_1731_0015, g32p_row07_traceSegment_024_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_024 1701 60 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1701 30 30, g32p_row07_traceSegment_024_1701_0030, g32p_row07_traceSegment_024_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1761 15 15, g32p_row07_traceSegment_024_1761_0015, g32p_row07_traceSegment_024_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1791 15 16, g32p_row07_traceSegment_024_1791_0015, g32p_row07_traceSegment_024_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1761 30 31, g32p_row07_traceSegment_024_1761_0030, g32p_row07_traceSegment_024_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_024 1701 121 = [4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1701 60 61, g32p_row07_traceSegment_024_1701_0060, g32p_row07_traceSegment_024_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1822 15 15, g32p_row07_traceSegment_024_1822_0015, g32p_row07_traceSegment_024_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1852 15 16, g32p_row07_traceSegment_024_1852_0015, g32p_row07_traceSegment_024_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1822 30 31, g32p_row07_traceSegment_024_1822_0030, g32p_row07_traceSegment_024_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1898 15 = [1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_024 1883 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1883 15 15, g32p_row07_traceSegment_024_1883_0015, g32p_row07_traceSegment_024_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_024 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_024 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_024_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_024 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1913 15 16, g32p_row07_traceSegment_024_1913_0015, g32p_row07_traceSegment_024_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_024 1883 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1883 30 31, g32p_row07_traceSegment_024_1883_0030, g32p_row07_traceSegment_024_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_024 1822 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1822 61 61, g32p_row07_traceSegment_024_1822_0061, g32p_row07_traceSegment_024_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_024 1701 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1701 121 122, g32p_row07_traceSegment_024_1701_0121, g32p_row07_traceSegment_024_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_024_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_024 1458 486 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 1458 243 243, g32p_row07_traceSegment_024_1458_0243, g32p_row07_traceSegment_024_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_024 972 972 = [5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 972 486 486, g32p_row07_traceSegment_024_0972_0486, g32p_row07_traceSegment_024_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_024_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_024 0 1944 = [6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_024 0 972 972, g32p_row07_traceSegment_024_0000_0972, g32p_row07_traceSegment_024_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 24 = [6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_024_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_028 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 28 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_028_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 0 15 15, g32p_row07_traceSegment_028_0000_0015, g32p_row07_traceSegment_028_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 30 15 15, g32p_row07_traceSegment_028_0030_0015, g32p_row07_traceSegment_028_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_028 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 0 30 30, g32p_row07_traceSegment_028_0000_0030, g32p_row07_traceSegment_028_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 60 15 15, g32p_row07_traceSegment_028_0060_0015, g32p_row07_traceSegment_028_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 90 15 16, g32p_row07_traceSegment_028_0090_0015, g32p_row07_traceSegment_028_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 60 30 31, g32p_row07_traceSegment_028_0060_0030, g32p_row07_traceSegment_028_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_028 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 0 60 61, g32p_row07_traceSegment_028_0000_0060, g32p_row07_traceSegment_028_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 121 15 15, g32p_row07_traceSegment_028_0121_0015, g32p_row07_traceSegment_028_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 151 15 16, g32p_row07_traceSegment_028_0151_0015, g32p_row07_traceSegment_028_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 121 30 31, g32p_row07_traceSegment_028_0121_0030, g32p_row07_traceSegment_028_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 182 15 15, g32p_row07_traceSegment_028_0182_0015, g32p_row07_traceSegment_028_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 212 15 16, g32p_row07_traceSegment_028_0212_0015, g32p_row07_traceSegment_028_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 182 30 31, g32p_row07_traceSegment_028_0182_0030, g32p_row07_traceSegment_028_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_028 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 121 61 61, g32p_row07_traceSegment_028_0121_0061, g32p_row07_traceSegment_028_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_028 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 0 121 122, g32p_row07_traceSegment_028_0000_0121, g32p_row07_traceSegment_028_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 243 15 15, g32p_row07_traceSegment_028_0243_0015, g32p_row07_traceSegment_028_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 273 15 15, g32p_row07_traceSegment_028_0273_0015, g32p_row07_traceSegment_028_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_028 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 243 30 30, g32p_row07_traceSegment_028_0243_0030, g32p_row07_traceSegment_028_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 303 15 15, g32p_row07_traceSegment_028_0303_0015, g32p_row07_traceSegment_028_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 333 15 16, g32p_row07_traceSegment_028_0333_0015, g32p_row07_traceSegment_028_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 303 30 31, g32p_row07_traceSegment_028_0303_0030, g32p_row07_traceSegment_028_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_028 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 243 60 61, g32p_row07_traceSegment_028_0243_0060, g32p_row07_traceSegment_028_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 364 15 15, g32p_row07_traceSegment_028_0364_0015, g32p_row07_traceSegment_028_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 394 15 16, g32p_row07_traceSegment_028_0394_0015, g32p_row07_traceSegment_028_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 364 30 31, g32p_row07_traceSegment_028_0364_0030, g32p_row07_traceSegment_028_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 425 15 15, g32p_row07_traceSegment_028_0425_0015, g32p_row07_traceSegment_028_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 455 15 16, g32p_row07_traceSegment_028_0455_0015, g32p_row07_traceSegment_028_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 425 30 31, g32p_row07_traceSegment_028_0425_0030, g32p_row07_traceSegment_028_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_028 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 364 61 61, g32p_row07_traceSegment_028_0364_0061, g32p_row07_traceSegment_028_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_028 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 243 121 122, g32p_row07_traceSegment_028_0243_0121, g32p_row07_traceSegment_028_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_028 0 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 0 243 243, g32p_row07_traceSegment_028_0000_0243, g32p_row07_traceSegment_028_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 486 15 15, g32p_row07_traceSegment_028_0486_0015, g32p_row07_traceSegment_028_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 516 15 15, g32p_row07_traceSegment_028_0516_0015, g32p_row07_traceSegment_028_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_028 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 486 30 30, g32p_row07_traceSegment_028_0486_0030, g32p_row07_traceSegment_028_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 546 15 15, g32p_row07_traceSegment_028_0546_0015, g32p_row07_traceSegment_028_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 576 15 16, g32p_row07_traceSegment_028_0576_0015, g32p_row07_traceSegment_028_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 546 30 31, g32p_row07_traceSegment_028_0546_0030, g32p_row07_traceSegment_028_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_028 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 486 60 61, g32p_row07_traceSegment_028_0486_0060, g32p_row07_traceSegment_028_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 607 15 15, g32p_row07_traceSegment_028_0607_0015, g32p_row07_traceSegment_028_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 637 15 16, g32p_row07_traceSegment_028_0637_0015, g32p_row07_traceSegment_028_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 607 30 31, g32p_row07_traceSegment_028_0607_0030, g32p_row07_traceSegment_028_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 668 15 15, g32p_row07_traceSegment_028_0668_0015, g32p_row07_traceSegment_028_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 698 15 16, g32p_row07_traceSegment_028_0698_0015, g32p_row07_traceSegment_028_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 668 30 31, g32p_row07_traceSegment_028_0668_0030, g32p_row07_traceSegment_028_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_028 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 607 61 61, g32p_row07_traceSegment_028_0607_0061, g32p_row07_traceSegment_028_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_028 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 486 121 122, g32p_row07_traceSegment_028_0486_0121, g32p_row07_traceSegment_028_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 729 15 15, g32p_row07_traceSegment_028_0729_0015, g32p_row07_traceSegment_028_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 759 15 15, g32p_row07_traceSegment_028_0759_0015, g32p_row07_traceSegment_028_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_028 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 729 30 30, g32p_row07_traceSegment_028_0729_0030, g32p_row07_traceSegment_028_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 789 15 15, g32p_row07_traceSegment_028_0789_0015, g32p_row07_traceSegment_028_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 819 15 16, g32p_row07_traceSegment_028_0819_0015, g32p_row07_traceSegment_028_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 789 30 31, g32p_row07_traceSegment_028_0789_0030, g32p_row07_traceSegment_028_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_028 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 729 60 61, g32p_row07_traceSegment_028_0729_0060, g32p_row07_traceSegment_028_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 850 15 15, g32p_row07_traceSegment_028_0850_0015, g32p_row07_traceSegment_028_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 880 15 16, g32p_row07_traceSegment_028_0880_0015, g32p_row07_traceSegment_028_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 850 30 31, g32p_row07_traceSegment_028_0850_0030, g32p_row07_traceSegment_028_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 911 15 15, g32p_row07_traceSegment_028_0911_0015, g32p_row07_traceSegment_028_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 941 15 16, g32p_row07_traceSegment_028_0941_0015, g32p_row07_traceSegment_028_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 911 30 31, g32p_row07_traceSegment_028_0911_0030, g32p_row07_traceSegment_028_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_028 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 850 61 61, g32p_row07_traceSegment_028_0850_0061, g32p_row07_traceSegment_028_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_028 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 729 121 122, g32p_row07_traceSegment_028_0729_0121, g32p_row07_traceSegment_028_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_028 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 486 243 243, g32p_row07_traceSegment_028_0486_0243, g32p_row07_traceSegment_028_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_028 0 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 0 486 486, g32p_row07_traceSegment_028_0000_0486, g32p_row07_traceSegment_028_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 972 15 15, g32p_row07_traceSegment_028_0972_0015, g32p_row07_traceSegment_028_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1002 15 15, g32p_row07_traceSegment_028_1002_0015, g32p_row07_traceSegment_028_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_028 972 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 972 30 30, g32p_row07_traceSegment_028_0972_0030, g32p_row07_traceSegment_028_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1032 15 15, g32p_row07_traceSegment_028_1032_0015, g32p_row07_traceSegment_028_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1062 15 16, g32p_row07_traceSegment_028_1062_0015, g32p_row07_traceSegment_028_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1032 30 31, g32p_row07_traceSegment_028_1032_0030, g32p_row07_traceSegment_028_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_028 972 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 972 60 61, g32p_row07_traceSegment_028_0972_0060, g32p_row07_traceSegment_028_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1093 15 15, g32p_row07_traceSegment_028_1093_0015, g32p_row07_traceSegment_028_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1123 15 16, g32p_row07_traceSegment_028_1123_0015, g32p_row07_traceSegment_028_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1093 30 31, g32p_row07_traceSegment_028_1093_0030, g32p_row07_traceSegment_028_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1154 15 15, g32p_row07_traceSegment_028_1154_0015, g32p_row07_traceSegment_028_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1184 15 16, g32p_row07_traceSegment_028_1184_0015, g32p_row07_traceSegment_028_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1154 30 31, g32p_row07_traceSegment_028_1154_0030, g32p_row07_traceSegment_028_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_028 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1093 61 61, g32p_row07_traceSegment_028_1093_0061, g32p_row07_traceSegment_028_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_028 972 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 972 121 122, g32p_row07_traceSegment_028_0972_0121, g32p_row07_traceSegment_028_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1215 15 15, g32p_row07_traceSegment_028_1215_0015, g32p_row07_traceSegment_028_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1245 15 15, g32p_row07_traceSegment_028_1245_0015, g32p_row07_traceSegment_028_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_028 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1215 30 30, g32p_row07_traceSegment_028_1215_0030, g32p_row07_traceSegment_028_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1290 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1275 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1275 15 15, g32p_row07_traceSegment_028_1275_0015, g32p_row07_traceSegment_028_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1305 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1305 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1305 15 16, g32p_row07_traceSegment_028_1305_0015, g32p_row07_traceSegment_028_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1275 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1275 30 31, g32p_row07_traceSegment_028_1275_0030, g32p_row07_traceSegment_028_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_028 1215 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1215 60 61, g32p_row07_traceSegment_028_1215_0060, g32p_row07_traceSegment_028_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1336 15 15, g32p_row07_traceSegment_028_1336_0015, g32p_row07_traceSegment_028_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1366 15 16, g32p_row07_traceSegment_028_1366_0015, g32p_row07_traceSegment_028_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1336 30 31, g32p_row07_traceSegment_028_1336_0030, g32p_row07_traceSegment_028_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1397 15 15, g32p_row07_traceSegment_028_1397_0015, g32p_row07_traceSegment_028_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1427 15 16, g32p_row07_traceSegment_028_1427_0015, g32p_row07_traceSegment_028_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1397 30 31, g32p_row07_traceSegment_028_1397_0030, g32p_row07_traceSegment_028_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_028 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1336 61 61, g32p_row07_traceSegment_028_1336_0061, g32p_row07_traceSegment_028_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_028 1215 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1215 121 122, g32p_row07_traceSegment_028_1215_0121, g32p_row07_traceSegment_028_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_028 972 486 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 972 243 243, g32p_row07_traceSegment_028_0972_0243, g32p_row07_traceSegment_028_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1458 15 15, g32p_row07_traceSegment_028_1458_0015, g32p_row07_traceSegment_028_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1488 15 15, g32p_row07_traceSegment_028_1488_0015, g32p_row07_traceSegment_028_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_028 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1458 30 30, g32p_row07_traceSegment_028_1458_0030, g32p_row07_traceSegment_028_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1518 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1518 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1518 15 15, g32p_row07_traceSegment_028_1518_0015, g32p_row07_traceSegment_028_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1563 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1548 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1548 15 16, g32p_row07_traceSegment_028_1548_0015, g32p_row07_traceSegment_028_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1518 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1518 30 31, g32p_row07_traceSegment_028_1518_0030, g32p_row07_traceSegment_028_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_028 1458 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1458 60 61, g32p_row07_traceSegment_028_1458_0060, g32p_row07_traceSegment_028_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1579 15 15, g32p_row07_traceSegment_028_1579_0015, g32p_row07_traceSegment_028_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1609 15 16, g32p_row07_traceSegment_028_1609_0015, g32p_row07_traceSegment_028_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1579 30 31, g32p_row07_traceSegment_028_1579_0030, g32p_row07_traceSegment_028_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1640 15 15, g32p_row07_traceSegment_028_1640_0015, g32p_row07_traceSegment_028_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1670 15 16, g32p_row07_traceSegment_028_1670_0015, g32p_row07_traceSegment_028_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1640 30 31, g32p_row07_traceSegment_028_1640_0030, g32p_row07_traceSegment_028_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_028 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1579 61 61, g32p_row07_traceSegment_028_1579_0061, g32p_row07_traceSegment_028_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_028 1458 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1458 121 122, g32p_row07_traceSegment_028_1458_0121, g32p_row07_traceSegment_028_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1701 15 15, g32p_row07_traceSegment_028_1701_0015, g32p_row07_traceSegment_028_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1731 15 15, g32p_row07_traceSegment_028_1731_0015, g32p_row07_traceSegment_028_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_028 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1701 30 30, g32p_row07_traceSegment_028_1701_0030, g32p_row07_traceSegment_028_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1761 15 15, g32p_row07_traceSegment_028_1761_0015, g32p_row07_traceSegment_028_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1791 15 16, g32p_row07_traceSegment_028_1791_0015, g32p_row07_traceSegment_028_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1761 30 31, g32p_row07_traceSegment_028_1761_0030, g32p_row07_traceSegment_028_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_028 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1701 60 61, g32p_row07_traceSegment_028_1701_0060, g32p_row07_traceSegment_028_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1822 15 15, g32p_row07_traceSegment_028_1822_0015, g32p_row07_traceSegment_028_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1852 15 16, g32p_row07_traceSegment_028_1852_0015, g32p_row07_traceSegment_028_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1822 30 31, g32p_row07_traceSegment_028_1822_0030, g32p_row07_traceSegment_028_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_028 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1883 15 15, g32p_row07_traceSegment_028_1883_0015, g32p_row07_traceSegment_028_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_028 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_028 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_028_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_028 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1913 15 16, g32p_row07_traceSegment_028_1913_0015, g32p_row07_traceSegment_028_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_028 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1883 30 31, g32p_row07_traceSegment_028_1883_0030, g32p_row07_traceSegment_028_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_028 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1822 61 61, g32p_row07_traceSegment_028_1822_0061, g32p_row07_traceSegment_028_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_028 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1701 121 122, g32p_row07_traceSegment_028_1701_0121, g32p_row07_traceSegment_028_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_028_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_028 1458 486 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 1458 243 243, g32p_row07_traceSegment_028_1458_0243, g32p_row07_traceSegment_028_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_028 972 972 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 972 486 486, g32p_row07_traceSegment_028_0972_0486, g32p_row07_traceSegment_028_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_028_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_028 0 1944 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_028 0 972 972, g32p_row07_traceSegment_028_0000_0972, g32p_row07_traceSegment_028_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 28 = [0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_028_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_030 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 30 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_030_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 0 15 15, g32p_row07_traceSegment_030_0000_0015, g32p_row07_traceSegment_030_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 30 15 15, g32p_row07_traceSegment_030_0030_0015, g32p_row07_traceSegment_030_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_030 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 0 30 30, g32p_row07_traceSegment_030_0000_0030, g32p_row07_traceSegment_030_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 60 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 60 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 60 15 15, g32p_row07_traceSegment_030_0060_0015, g32p_row07_traceSegment_030_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 90 15 16, g32p_row07_traceSegment_030_0090_0015, g32p_row07_traceSegment_030_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 60 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 60 30 31, g32p_row07_traceSegment_030_0060_0030, g32p_row07_traceSegment_030_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_030 0 121 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 0 60 61, g32p_row07_traceSegment_030_0000_0060, g32p_row07_traceSegment_030_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 121 15 15, g32p_row07_traceSegment_030_0121_0015, g32p_row07_traceSegment_030_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 151 15 16, g32p_row07_traceSegment_030_0151_0015, g32p_row07_traceSegment_030_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 121 30 31, g32p_row07_traceSegment_030_0121_0030, g32p_row07_traceSegment_030_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 182 15 15, g32p_row07_traceSegment_030_0182_0015, g32p_row07_traceSegment_030_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 212 15 16, g32p_row07_traceSegment_030_0212_0015, g32p_row07_traceSegment_030_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 182 30 31, g32p_row07_traceSegment_030_0182_0030, g32p_row07_traceSegment_030_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_030 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 121 61 61, g32p_row07_traceSegment_030_0121_0061, g32p_row07_traceSegment_030_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_030 0 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 0 121 122, g32p_row07_traceSegment_030_0000_0121, g32p_row07_traceSegment_030_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 243 15 15, g32p_row07_traceSegment_030_0243_0015, g32p_row07_traceSegment_030_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 273 15 15, g32p_row07_traceSegment_030_0273_0015, g32p_row07_traceSegment_030_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_030 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 243 30 30, g32p_row07_traceSegment_030_0243_0030, g32p_row07_traceSegment_030_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 303 15 15, g32p_row07_traceSegment_030_0303_0015, g32p_row07_traceSegment_030_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 333 15 16, g32p_row07_traceSegment_030_0333_0015, g32p_row07_traceSegment_030_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 303 30 31, g32p_row07_traceSegment_030_0303_0030, g32p_row07_traceSegment_030_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_030 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 243 60 61, g32p_row07_traceSegment_030_0243_0060, g32p_row07_traceSegment_030_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 364 15 15, g32p_row07_traceSegment_030_0364_0015, g32p_row07_traceSegment_030_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 394 15 16, g32p_row07_traceSegment_030_0394_0015, g32p_row07_traceSegment_030_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 364 30 31, g32p_row07_traceSegment_030_0364_0030, g32p_row07_traceSegment_030_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 425 15 15, g32p_row07_traceSegment_030_0425_0015, g32p_row07_traceSegment_030_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 455 15 16, g32p_row07_traceSegment_030_0455_0015, g32p_row07_traceSegment_030_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 425 30 31, g32p_row07_traceSegment_030_0425_0030, g32p_row07_traceSegment_030_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_030 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 364 61 61, g32p_row07_traceSegment_030_0364_0061, g32p_row07_traceSegment_030_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_030 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 243 121 122, g32p_row07_traceSegment_030_0243_0121, g32p_row07_traceSegment_030_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_030 0 486 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 0 243 243, g32p_row07_traceSegment_030_0000_0243, g32p_row07_traceSegment_030_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 486 15 15, g32p_row07_traceSegment_030_0486_0015, g32p_row07_traceSegment_030_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 516 15 15, g32p_row07_traceSegment_030_0516_0015, g32p_row07_traceSegment_030_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_030 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 486 30 30, g32p_row07_traceSegment_030_0486_0030, g32p_row07_traceSegment_030_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 546 15 15, g32p_row07_traceSegment_030_0546_0015, g32p_row07_traceSegment_030_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 576 15 16, g32p_row07_traceSegment_030_0576_0015, g32p_row07_traceSegment_030_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 546 30 31, g32p_row07_traceSegment_030_0546_0030, g32p_row07_traceSegment_030_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_030 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 486 60 61, g32p_row07_traceSegment_030_0486_0060, g32p_row07_traceSegment_030_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 607 15 15, g32p_row07_traceSegment_030_0607_0015, g32p_row07_traceSegment_030_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 637 15 16, g32p_row07_traceSegment_030_0637_0015, g32p_row07_traceSegment_030_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 607 30 31, g32p_row07_traceSegment_030_0607_0030, g32p_row07_traceSegment_030_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 668 15 15, g32p_row07_traceSegment_030_0668_0015, g32p_row07_traceSegment_030_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 698 15 16, g32p_row07_traceSegment_030_0698_0015, g32p_row07_traceSegment_030_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 668 30 31, g32p_row07_traceSegment_030_0668_0030, g32p_row07_traceSegment_030_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_030 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 607 61 61, g32p_row07_traceSegment_030_0607_0061, g32p_row07_traceSegment_030_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_030 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 486 121 122, g32p_row07_traceSegment_030_0486_0121, g32p_row07_traceSegment_030_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 729 15 15, g32p_row07_traceSegment_030_0729_0015, g32p_row07_traceSegment_030_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 774 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 759 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 759 15 15, g32p_row07_traceSegment_030_0759_0015, g32p_row07_traceSegment_030_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_030 729 60 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 729 30 30, g32p_row07_traceSegment_030_0729_0030, g32p_row07_traceSegment_030_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 789 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 789 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 789 15 15, g32p_row07_traceSegment_030_0789_0015, g32p_row07_traceSegment_030_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 819 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 819 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 819 15 16, g32p_row07_traceSegment_030_0819_0015, g32p_row07_traceSegment_030_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 789 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 789 30 31, g32p_row07_traceSegment_030_0789_0030, g32p_row07_traceSegment_030_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_030 729 121 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 729 60 61, g32p_row07_traceSegment_030_0729_0060, g32p_row07_traceSegment_030_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 850 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 865 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 850 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 850 15 15, g32p_row07_traceSegment_030_0850_0015, g32p_row07_traceSegment_030_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 895 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 880 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 880 15 16, g32p_row07_traceSegment_030_0880_0015, g32p_row07_traceSegment_030_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 850 61 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 850 30 31, g32p_row07_traceSegment_030_0850_0030, g32p_row07_traceSegment_030_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 926 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 911 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 911 15 15, g32p_row07_traceSegment_030_0911_0015, g32p_row07_traceSegment_030_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 941 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 956 16 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 941 31 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 941 15 16, g32p_row07_traceSegment_030_0941_0015, g32p_row07_traceSegment_030_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 911 61 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 911 30 31, g32p_row07_traceSegment_030_0911_0030, g32p_row07_traceSegment_030_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_030 850 122 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 850 61 61, g32p_row07_traceSegment_030_0850_0061, g32p_row07_traceSegment_030_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_030 729 243 = [0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 729 121 122, g32p_row07_traceSegment_030_0729_0121, g32p_row07_traceSegment_030_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_030 486 486 = [0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 486 243 243, g32p_row07_traceSegment_030_0486_0243, g32p_row07_traceSegment_030_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_030 0 972 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 0 486 486, g32p_row07_traceSegment_030_0000_0486, g32p_row07_traceSegment_030_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 972 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 987 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 972 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 972 15 15, g32p_row07_traceSegment_030_0972_0015, g32p_row07_traceSegment_030_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1002 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1017 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1002 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1002 15 15, g32p_row07_traceSegment_030_1002_0015, g32p_row07_traceSegment_030_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_030 972 60 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 972 30 30, g32p_row07_traceSegment_030_0972_0030, g32p_row07_traceSegment_030_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1032 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1047 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1032 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1032 15 15, g32p_row07_traceSegment_030_1032_0015, g32p_row07_traceSegment_030_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1062 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1077 16 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1062 31 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1062 15 16, g32p_row07_traceSegment_030_1062_0015, g32p_row07_traceSegment_030_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1032 61 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1032 30 31, g32p_row07_traceSegment_030_1032_0030, g32p_row07_traceSegment_030_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_030 972 121 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 972 60 61, g32p_row07_traceSegment_030_0972_0060, g32p_row07_traceSegment_030_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1093 15 = [0, 0, 8] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1108 15 = [0, 0, 8] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1093 30 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1093 15 15, g32p_row07_traceSegment_030_1093_0015, g32p_row07_traceSegment_030_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1123 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1138 16 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1123 31 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1123 15 16, g32p_row07_traceSegment_030_1123_0015, g32p_row07_traceSegment_030_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1093 61 = [0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1093 30 31, g32p_row07_traceSegment_030_1093_0030, g32p_row07_traceSegment_030_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1154 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1154 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1154 15 15, g32p_row07_traceSegment_030_1154_0015, g32p_row07_traceSegment_030_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1184 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1199 16 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1184 31 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1184 15 16, g32p_row07_traceSegment_030_1184_0015, g32p_row07_traceSegment_030_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1154 61 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1154 30 31, g32p_row07_traceSegment_030_1154_0030, g32p_row07_traceSegment_030_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_030 1093 122 = [0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1093 61 61, g32p_row07_traceSegment_030_1093_0061, g32p_row07_traceSegment_030_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_030 972 243 = [0, 0, 53] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 972 121 122, g32p_row07_traceSegment_030_0972_0121, g32p_row07_traceSegment_030_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1215 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1230 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1215 30 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1215 15 15, g32p_row07_traceSegment_030_1215_0015, g32p_row07_traceSegment_030_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1245 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1260 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1245 30 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1245 15 15, g32p_row07_traceSegment_030_1245_0015, g32p_row07_traceSegment_030_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_030 1215 60 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1215 30 30, g32p_row07_traceSegment_030_1215_0030, g32p_row07_traceSegment_030_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1275 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1275 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1275 15 15, g32p_row07_traceSegment_030_1275_0015, g32p_row07_traceSegment_030_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1305 15 16, g32p_row07_traceSegment_030_1305_0015, g32p_row07_traceSegment_030_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1275 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1275 30 31, g32p_row07_traceSegment_030_1275_0030, g32p_row07_traceSegment_030_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_030 1215 121 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1215 60 61, g32p_row07_traceSegment_030_1215_0060, g32p_row07_traceSegment_030_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1336 15 15, g32p_row07_traceSegment_030_1336_0015, g32p_row07_traceSegment_030_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1366 15 16, g32p_row07_traceSegment_030_1366_0015, g32p_row07_traceSegment_030_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1336 30 31, g32p_row07_traceSegment_030_1336_0030, g32p_row07_traceSegment_030_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1397 15 15, g32p_row07_traceSegment_030_1397_0015, g32p_row07_traceSegment_030_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1427 15 16, g32p_row07_traceSegment_030_1427_0015, g32p_row07_traceSegment_030_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1397 30 31, g32p_row07_traceSegment_030_1397_0030, g32p_row07_traceSegment_030_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_030 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1336 61 61, g32p_row07_traceSegment_030_1336_0061, g32p_row07_traceSegment_030_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_030 1215 243 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1215 121 122, g32p_row07_traceSegment_030_1215_0121, g32p_row07_traceSegment_030_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_030 972 486 = [0, 0, 72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 972 243 243, g32p_row07_traceSegment_030_0972_0243, g32p_row07_traceSegment_030_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1458 15 15, g32p_row07_traceSegment_030_1458_0015, g32p_row07_traceSegment_030_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1488 15 15, g32p_row07_traceSegment_030_1488_0015, g32p_row07_traceSegment_030_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_030 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1458 30 30, g32p_row07_traceSegment_030_1458_0030, g32p_row07_traceSegment_030_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1518 15 15, g32p_row07_traceSegment_030_1518_0015, g32p_row07_traceSegment_030_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1548 15 16, g32p_row07_traceSegment_030_1548_0015, g32p_row07_traceSegment_030_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1518 30 31, g32p_row07_traceSegment_030_1518_0030, g32p_row07_traceSegment_030_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_030 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1458 60 61, g32p_row07_traceSegment_030_1458_0060, g32p_row07_traceSegment_030_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1579 15 15, g32p_row07_traceSegment_030_1579_0015, g32p_row07_traceSegment_030_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1609 15 16, g32p_row07_traceSegment_030_1609_0015, g32p_row07_traceSegment_030_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1579 30 31, g32p_row07_traceSegment_030_1579_0030, g32p_row07_traceSegment_030_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1640 15 15, g32p_row07_traceSegment_030_1640_0015, g32p_row07_traceSegment_030_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1670 15 16, g32p_row07_traceSegment_030_1670_0015, g32p_row07_traceSegment_030_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1640 30 31, g32p_row07_traceSegment_030_1640_0030, g32p_row07_traceSegment_030_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_030 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1579 61 61, g32p_row07_traceSegment_030_1579_0061, g32p_row07_traceSegment_030_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_030 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1458 121 122, g32p_row07_traceSegment_030_1458_0121, g32p_row07_traceSegment_030_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1701 15 15, g32p_row07_traceSegment_030_1701_0015, g32p_row07_traceSegment_030_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1731 15 15, g32p_row07_traceSegment_030_1731_0015, g32p_row07_traceSegment_030_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_030 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1701 30 30, g32p_row07_traceSegment_030_1701_0030, g32p_row07_traceSegment_030_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1761 15 15, g32p_row07_traceSegment_030_1761_0015, g32p_row07_traceSegment_030_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1791 15 16, g32p_row07_traceSegment_030_1791_0015, g32p_row07_traceSegment_030_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1761 30 31, g32p_row07_traceSegment_030_1761_0030, g32p_row07_traceSegment_030_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_030 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1701 60 61, g32p_row07_traceSegment_030_1701_0060, g32p_row07_traceSegment_030_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1822 15 15, g32p_row07_traceSegment_030_1822_0015, g32p_row07_traceSegment_030_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1852 15 16, g32p_row07_traceSegment_030_1852_0015, g32p_row07_traceSegment_030_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1822 30 31, g32p_row07_traceSegment_030_1822_0030, g32p_row07_traceSegment_030_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_030 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1883 15 15, g32p_row07_traceSegment_030_1883_0015, g32p_row07_traceSegment_030_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_030 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_030 1928 16 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_030_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_030 1913 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1913 15 16, g32p_row07_traceSegment_030_1913_0015, g32p_row07_traceSegment_030_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_030 1883 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1883 30 31, g32p_row07_traceSegment_030_1883_0030, g32p_row07_traceSegment_030_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_030 1822 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1822 61 61, g32p_row07_traceSegment_030_1822_0061, g32p_row07_traceSegment_030_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_030 1701 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1701 121 122, g32p_row07_traceSegment_030_1701_0121, g32p_row07_traceSegment_030_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_030_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_030 1458 486 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 1458 243 243, g32p_row07_traceSegment_030_1458_0243, g32p_row07_traceSegment_030_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_030 972 972 = [0, 0, 76] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 972 486 486, g32p_row07_traceSegment_030_0972_0486, g32p_row07_traceSegment_030_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_030_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_030 0 1944 = [0, 0, 108] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_030 0 972 972, g32p_row07_traceSegment_030_0000_0972, g32p_row07_traceSegment_030_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_030 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 30 = [0, 0, 108] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_030_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_032 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 32 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_032_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 0 15 15, g32p_row07_traceSegment_032_0000_0015, g32p_row07_traceSegment_032_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 30 15 15, g32p_row07_traceSegment_032_0030_0015, g32p_row07_traceSegment_032_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_032 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 0 30 30, g32p_row07_traceSegment_032_0000_0030, g32p_row07_traceSegment_032_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 60 15 = [0, 0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 75 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 60 30 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 60 15 15, g32p_row07_traceSegment_032_0060_0015, g32p_row07_traceSegment_032_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 90 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 90 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 90 15 16, g32p_row07_traceSegment_032_0090_0015, g32p_row07_traceSegment_032_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 60 61 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 60 30 31, g32p_row07_traceSegment_032_0060_0030, g32p_row07_traceSegment_032_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_032 0 121 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 0 60 61, g32p_row07_traceSegment_032_0000_0060, g32p_row07_traceSegment_032_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 136 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 121 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 121 15 15, g32p_row07_traceSegment_032_0121_0015, g32p_row07_traceSegment_032_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 151 15 16, g32p_row07_traceSegment_032_0151_0015, g32p_row07_traceSegment_032_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 121 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 121 30 31, g32p_row07_traceSegment_032_0121_0030, g32p_row07_traceSegment_032_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 182 15 15, g32p_row07_traceSegment_032_0182_0015, g32p_row07_traceSegment_032_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 212 15 16, g32p_row07_traceSegment_032_0212_0015, g32p_row07_traceSegment_032_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 182 30 31, g32p_row07_traceSegment_032_0182_0030, g32p_row07_traceSegment_032_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_032 121 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 121 61 61, g32p_row07_traceSegment_032_0121_0061, g32p_row07_traceSegment_032_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_032 0 243 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 0 121 122, g32p_row07_traceSegment_032_0000_0121, g32p_row07_traceSegment_032_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 243 15 15, g32p_row07_traceSegment_032_0243_0015, g32p_row07_traceSegment_032_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 273 15 15, g32p_row07_traceSegment_032_0273_0015, g32p_row07_traceSegment_032_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_032 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 243 30 30, g32p_row07_traceSegment_032_0243_0030, g32p_row07_traceSegment_032_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 303 15 15, g32p_row07_traceSegment_032_0303_0015, g32p_row07_traceSegment_032_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 333 15 16, g32p_row07_traceSegment_032_0333_0015, g32p_row07_traceSegment_032_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 303 30 31, g32p_row07_traceSegment_032_0303_0030, g32p_row07_traceSegment_032_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_032 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 243 60 61, g32p_row07_traceSegment_032_0243_0060, g32p_row07_traceSegment_032_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 364 15 15, g32p_row07_traceSegment_032_0364_0015, g32p_row07_traceSegment_032_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 394 15 16, g32p_row07_traceSegment_032_0394_0015, g32p_row07_traceSegment_032_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 364 30 31, g32p_row07_traceSegment_032_0364_0030, g32p_row07_traceSegment_032_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 425 15 15, g32p_row07_traceSegment_032_0425_0015, g32p_row07_traceSegment_032_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 455 15 16, g32p_row07_traceSegment_032_0455_0015, g32p_row07_traceSegment_032_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 425 30 31, g32p_row07_traceSegment_032_0425_0030, g32p_row07_traceSegment_032_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_032 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 364 61 61, g32p_row07_traceSegment_032_0364_0061, g32p_row07_traceSegment_032_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_032 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 243 121 122, g32p_row07_traceSegment_032_0243_0121, g32p_row07_traceSegment_032_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_032 0 486 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 0 243 243, g32p_row07_traceSegment_032_0000_0243, g32p_row07_traceSegment_032_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 486 15 15, g32p_row07_traceSegment_032_0486_0015, g32p_row07_traceSegment_032_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 516 15 15, g32p_row07_traceSegment_032_0516_0015, g32p_row07_traceSegment_032_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_032 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 486 30 30, g32p_row07_traceSegment_032_0486_0030, g32p_row07_traceSegment_032_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 546 15 15, g32p_row07_traceSegment_032_0546_0015, g32p_row07_traceSegment_032_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 576 15 16, g32p_row07_traceSegment_032_0576_0015, g32p_row07_traceSegment_032_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 546 30 31, g32p_row07_traceSegment_032_0546_0030, g32p_row07_traceSegment_032_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_032 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 486 60 61, g32p_row07_traceSegment_032_0486_0060, g32p_row07_traceSegment_032_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 607 15 15, g32p_row07_traceSegment_032_0607_0015, g32p_row07_traceSegment_032_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 637 15 16, g32p_row07_traceSegment_032_0637_0015, g32p_row07_traceSegment_032_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 607 30 31, g32p_row07_traceSegment_032_0607_0030, g32p_row07_traceSegment_032_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 668 15 15, g32p_row07_traceSegment_032_0668_0015, g32p_row07_traceSegment_032_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 698 15 16, g32p_row07_traceSegment_032_0698_0015, g32p_row07_traceSegment_032_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 668 30 31, g32p_row07_traceSegment_032_0668_0030, g32p_row07_traceSegment_032_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_032 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 607 61 61, g32p_row07_traceSegment_032_0607_0061, g32p_row07_traceSegment_032_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_032 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 486 121 122, g32p_row07_traceSegment_032_0486_0121, g32p_row07_traceSegment_032_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 729 15 15, g32p_row07_traceSegment_032_0729_0015, g32p_row07_traceSegment_032_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 774 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 759 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 759 15 15, g32p_row07_traceSegment_032_0759_0015, g32p_row07_traceSegment_032_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_032 729 60 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 729 30 30, g32p_row07_traceSegment_032_0729_0030, g32p_row07_traceSegment_032_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 804 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 789 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 789 15 15, g32p_row07_traceSegment_032_0789_0015, g32p_row07_traceSegment_032_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 819 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 819 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 819 15 16, g32p_row07_traceSegment_032_0819_0015, g32p_row07_traceSegment_032_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 789 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 789 30 31, g32p_row07_traceSegment_032_0789_0030, g32p_row07_traceSegment_032_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_032 729 121 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 729 60 61, g32p_row07_traceSegment_032_0729_0060, g32p_row07_traceSegment_032_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 850 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 865 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 850 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 850 15 15, g32p_row07_traceSegment_032_0850_0015, g32p_row07_traceSegment_032_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 880 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 895 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 880 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 880 15 16, g32p_row07_traceSegment_032_0880_0015, g32p_row07_traceSegment_032_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 850 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 850 30 31, g32p_row07_traceSegment_032_0850_0030, g32p_row07_traceSegment_032_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 911 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 926 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 911 30 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 911 15 15, g32p_row07_traceSegment_032_0911_0015, g32p_row07_traceSegment_032_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 941 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 956 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 941 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 941 15 16, g32p_row07_traceSegment_032_0941_0015, g32p_row07_traceSegment_032_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 911 61 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 911 30 31, g32p_row07_traceSegment_032_0911_0030, g32p_row07_traceSegment_032_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_032 850 122 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 850 61 61, g32p_row07_traceSegment_032_0850_0061, g32p_row07_traceSegment_032_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_032 729 243 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 729 121 122, g32p_row07_traceSegment_032_0729_0121, g32p_row07_traceSegment_032_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_032 486 486 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 486 243 243, g32p_row07_traceSegment_032_0486_0243, g32p_row07_traceSegment_032_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_032 0 972 = [0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 0 486 486, g32p_row07_traceSegment_032_0000_0486, g32p_row07_traceSegment_032_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 972 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 987 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 972 30 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 972 15 15, g32p_row07_traceSegment_032_0972_0015, g32p_row07_traceSegment_032_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1002 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1017 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1002 30 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1002 15 15, g32p_row07_traceSegment_032_1002_0015, g32p_row07_traceSegment_032_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_032 972 60 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 972 30 30, g32p_row07_traceSegment_032_0972_0030, g32p_row07_traceSegment_032_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1032 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1047 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1032 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1032 15 15, g32p_row07_traceSegment_032_1032_0015, g32p_row07_traceSegment_032_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1062 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1077 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1062 31 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1062 15 16, g32p_row07_traceSegment_032_1062_0015, g32p_row07_traceSegment_032_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1032 61 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1032 30 31, g32p_row07_traceSegment_032_1032_0030, g32p_row07_traceSegment_032_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_032 972 121 = [0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 972 60 61, g32p_row07_traceSegment_032_0972_0060, g32p_row07_traceSegment_032_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1093 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1108 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1093 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1093 15 15, g32p_row07_traceSegment_032_1093_0015, g32p_row07_traceSegment_032_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1123 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1123 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1123 15 16, g32p_row07_traceSegment_032_1123_0015, g32p_row07_traceSegment_032_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1093 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1093 30 31, g32p_row07_traceSegment_032_1093_0030, g32p_row07_traceSegment_032_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1154 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1169 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1154 30 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1154 15 15, g32p_row07_traceSegment_032_1154_0015, g32p_row07_traceSegment_032_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1184 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1199 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1184 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1184 15 16, g32p_row07_traceSegment_032_1184_0015, g32p_row07_traceSegment_032_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1154 61 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1154 30 31, g32p_row07_traceSegment_032_1154_0030, g32p_row07_traceSegment_032_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_032 1093 122 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1093 61 61, g32p_row07_traceSegment_032_1093_0061, g32p_row07_traceSegment_032_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_032 972 243 = [0, 0, 38] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 972 121 122, g32p_row07_traceSegment_032_0972_0121, g32p_row07_traceSegment_032_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1215 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1215 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1215 15 15, g32p_row07_traceSegment_032_1215_0015, g32p_row07_traceSegment_032_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1245 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1260 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1245 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1245 15 15, g32p_row07_traceSegment_032_1245_0015, g32p_row07_traceSegment_032_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_032 1215 60 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1215 30 30, g32p_row07_traceSegment_032_1215_0030, g32p_row07_traceSegment_032_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1275 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1275 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1275 15 15, g32p_row07_traceSegment_032_1275_0015, g32p_row07_traceSegment_032_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1305 15 16, g32p_row07_traceSegment_032_1305_0015, g32p_row07_traceSegment_032_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1275 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1275 30 31, g32p_row07_traceSegment_032_1275_0030, g32p_row07_traceSegment_032_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_032 1215 121 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1215 60 61, g32p_row07_traceSegment_032_1215_0060, g32p_row07_traceSegment_032_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1336 15 15, g32p_row07_traceSegment_032_1336_0015, g32p_row07_traceSegment_032_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1366 15 16, g32p_row07_traceSegment_032_1366_0015, g32p_row07_traceSegment_032_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1336 30 31, g32p_row07_traceSegment_032_1336_0030, g32p_row07_traceSegment_032_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1397 15 15, g32p_row07_traceSegment_032_1397_0015, g32p_row07_traceSegment_032_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1427 15 16, g32p_row07_traceSegment_032_1427_0015, g32p_row07_traceSegment_032_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1397 30 31, g32p_row07_traceSegment_032_1397_0030, g32p_row07_traceSegment_032_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_032 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1336 61 61, g32p_row07_traceSegment_032_1336_0061, g32p_row07_traceSegment_032_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_032 1215 243 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1215 121 122, g32p_row07_traceSegment_032_1215_0121, g32p_row07_traceSegment_032_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_032 972 486 = [0, 0, 45] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 972 243 243, g32p_row07_traceSegment_032_0972_0243, g32p_row07_traceSegment_032_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1458 15 15, g32p_row07_traceSegment_032_1458_0015, g32p_row07_traceSegment_032_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1488 15 15, g32p_row07_traceSegment_032_1488_0015, g32p_row07_traceSegment_032_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_032 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1458 30 30, g32p_row07_traceSegment_032_1458_0030, g32p_row07_traceSegment_032_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1518 15 15, g32p_row07_traceSegment_032_1518_0015, g32p_row07_traceSegment_032_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1548 15 16, g32p_row07_traceSegment_032_1548_0015, g32p_row07_traceSegment_032_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1518 30 31, g32p_row07_traceSegment_032_1518_0030, g32p_row07_traceSegment_032_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_032 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1458 60 61, g32p_row07_traceSegment_032_1458_0060, g32p_row07_traceSegment_032_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1579 15 15, g32p_row07_traceSegment_032_1579_0015, g32p_row07_traceSegment_032_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1609 15 16, g32p_row07_traceSegment_032_1609_0015, g32p_row07_traceSegment_032_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1579 30 31, g32p_row07_traceSegment_032_1579_0030, g32p_row07_traceSegment_032_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1640 15 15, g32p_row07_traceSegment_032_1640_0015, g32p_row07_traceSegment_032_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1670 15 16, g32p_row07_traceSegment_032_1670_0015, g32p_row07_traceSegment_032_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1640 30 31, g32p_row07_traceSegment_032_1640_0030, g32p_row07_traceSegment_032_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_032 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1579 61 61, g32p_row07_traceSegment_032_1579_0061, g32p_row07_traceSegment_032_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_032 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1458 121 122, g32p_row07_traceSegment_032_1458_0121, g32p_row07_traceSegment_032_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1701 15 15, g32p_row07_traceSegment_032_1701_0015, g32p_row07_traceSegment_032_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1731 15 15, g32p_row07_traceSegment_032_1731_0015, g32p_row07_traceSegment_032_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_032 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1701 30 30, g32p_row07_traceSegment_032_1701_0030, g32p_row07_traceSegment_032_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1761 15 15, g32p_row07_traceSegment_032_1761_0015, g32p_row07_traceSegment_032_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1791 15 16, g32p_row07_traceSegment_032_1791_0015, g32p_row07_traceSegment_032_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1761 30 31, g32p_row07_traceSegment_032_1761_0030, g32p_row07_traceSegment_032_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_032 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1701 60 61, g32p_row07_traceSegment_032_1701_0060, g32p_row07_traceSegment_032_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1822 15 15, g32p_row07_traceSegment_032_1822_0015, g32p_row07_traceSegment_032_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1852 15 16, g32p_row07_traceSegment_032_1852_0015, g32p_row07_traceSegment_032_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1822 30 31, g32p_row07_traceSegment_032_1822_0030, g32p_row07_traceSegment_032_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_032 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1883 15 15, g32p_row07_traceSegment_032_1883_0015, g32p_row07_traceSegment_032_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_032 1913 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_032 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_032_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_032 1913 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1913 15 16, g32p_row07_traceSegment_032_1913_0015, g32p_row07_traceSegment_032_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_032 1883 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1883 30 31, g32p_row07_traceSegment_032_1883_0030, g32p_row07_traceSegment_032_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_032 1822 122 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1822 61 61, g32p_row07_traceSegment_032_1822_0061, g32p_row07_traceSegment_032_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_032 1701 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1701 121 122, g32p_row07_traceSegment_032_1701_0121, g32p_row07_traceSegment_032_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_032_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_032 1458 486 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 1458 243 243, g32p_row07_traceSegment_032_1458_0243, g32p_row07_traceSegment_032_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_032 972 972 = [0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 972 486 486, g32p_row07_traceSegment_032_0972_0486, g32p_row07_traceSegment_032_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_032_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_032 0 1944 = [0, 0, 84] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_032 0 972 972, g32p_row07_traceSegment_032_0000_0972, g32p_row07_traceSegment_032_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 32 = [0, 0, 84] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_032_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_033 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 33 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_033_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 0 15 15, g32p_row07_traceSegment_033_0000_0015, g32p_row07_traceSegment_033_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 30 15 15, g32p_row07_traceSegment_033_0030_0015, g32p_row07_traceSegment_033_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_033 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 0 30 30, g32p_row07_traceSegment_033_0000_0030, g32p_row07_traceSegment_033_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 60 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 75 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 60 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 60 15 15, g32p_row07_traceSegment_033_0060_0015, g32p_row07_traceSegment_033_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 90 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 90 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 90 15 16, g32p_row07_traceSegment_033_0090_0015, g32p_row07_traceSegment_033_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 60 61 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 60 30 31, g32p_row07_traceSegment_033_0060_0030, g32p_row07_traceSegment_033_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_033 0 121 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 0 60 61, g32p_row07_traceSegment_033_0000_0060, g32p_row07_traceSegment_033_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 121 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 136 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 121 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 121 15 15, g32p_row07_traceSegment_033_0121_0015, g32p_row07_traceSegment_033_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 151 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 151 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 151 15 16, g32p_row07_traceSegment_033_0151_0015, g32p_row07_traceSegment_033_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 121 61 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 121 30 31, g32p_row07_traceSegment_033_0121_0030, g32p_row07_traceSegment_033_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 182 15 15, g32p_row07_traceSegment_033_0182_0015, g32p_row07_traceSegment_033_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 212 15 16, g32p_row07_traceSegment_033_0212_0015, g32p_row07_traceSegment_033_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 182 30 31, g32p_row07_traceSegment_033_0182_0030, g32p_row07_traceSegment_033_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_033 121 122 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 121 61 61, g32p_row07_traceSegment_033_0121_0061, g32p_row07_traceSegment_033_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_033 0 243 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 0 121 122, g32p_row07_traceSegment_033_0000_0121, g32p_row07_traceSegment_033_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 243 15 15, g32p_row07_traceSegment_033_0243_0015, g32p_row07_traceSegment_033_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 273 15 15, g32p_row07_traceSegment_033_0273_0015, g32p_row07_traceSegment_033_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_033 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 243 30 30, g32p_row07_traceSegment_033_0243_0030, g32p_row07_traceSegment_033_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 303 15 15, g32p_row07_traceSegment_033_0303_0015, g32p_row07_traceSegment_033_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 333 15 16, g32p_row07_traceSegment_033_0333_0015, g32p_row07_traceSegment_033_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 303 30 31, g32p_row07_traceSegment_033_0303_0030, g32p_row07_traceSegment_033_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_033 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 243 60 61, g32p_row07_traceSegment_033_0243_0060, g32p_row07_traceSegment_033_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 364 15 15, g32p_row07_traceSegment_033_0364_0015, g32p_row07_traceSegment_033_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 394 15 16, g32p_row07_traceSegment_033_0394_0015, g32p_row07_traceSegment_033_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 364 30 31, g32p_row07_traceSegment_033_0364_0030, g32p_row07_traceSegment_033_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 425 15 15, g32p_row07_traceSegment_033_0425_0015, g32p_row07_traceSegment_033_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 455 15 16, g32p_row07_traceSegment_033_0455_0015, g32p_row07_traceSegment_033_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 425 30 31, g32p_row07_traceSegment_033_0425_0030, g32p_row07_traceSegment_033_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_033 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 364 61 61, g32p_row07_traceSegment_033_0364_0061, g32p_row07_traceSegment_033_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_033 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 243 121 122, g32p_row07_traceSegment_033_0243_0121, g32p_row07_traceSegment_033_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_033 0 486 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 0 243 243, g32p_row07_traceSegment_033_0000_0243, g32p_row07_traceSegment_033_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 486 15 15, g32p_row07_traceSegment_033_0486_0015, g32p_row07_traceSegment_033_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 516 15 15, g32p_row07_traceSegment_033_0516_0015, g32p_row07_traceSegment_033_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_033 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 486 30 30, g32p_row07_traceSegment_033_0486_0030, g32p_row07_traceSegment_033_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 546 15 15, g32p_row07_traceSegment_033_0546_0015, g32p_row07_traceSegment_033_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 576 15 16, g32p_row07_traceSegment_033_0576_0015, g32p_row07_traceSegment_033_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 546 30 31, g32p_row07_traceSegment_033_0546_0030, g32p_row07_traceSegment_033_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_033 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 486 60 61, g32p_row07_traceSegment_033_0486_0060, g32p_row07_traceSegment_033_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 607 15 15, g32p_row07_traceSegment_033_0607_0015, g32p_row07_traceSegment_033_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 637 15 16, g32p_row07_traceSegment_033_0637_0015, g32p_row07_traceSegment_033_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 607 30 31, g32p_row07_traceSegment_033_0607_0030, g32p_row07_traceSegment_033_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 668 15 15, g32p_row07_traceSegment_033_0668_0015, g32p_row07_traceSegment_033_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 698 15 16, g32p_row07_traceSegment_033_0698_0015, g32p_row07_traceSegment_033_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 668 30 31, g32p_row07_traceSegment_033_0668_0030, g32p_row07_traceSegment_033_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_033 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 607 61 61, g32p_row07_traceSegment_033_0607_0061, g32p_row07_traceSegment_033_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_033 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 486 121 122, g32p_row07_traceSegment_033_0486_0121, g32p_row07_traceSegment_033_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 729 15 15, g32p_row07_traceSegment_033_0729_0015, g32p_row07_traceSegment_033_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 759 15 15, g32p_row07_traceSegment_033_0759_0015, g32p_row07_traceSegment_033_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_033 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 729 30 30, g32p_row07_traceSegment_033_0729_0030, g32p_row07_traceSegment_033_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 789 15 15, g32p_row07_traceSegment_033_0789_0015, g32p_row07_traceSegment_033_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 819 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 834 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 819 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 819 15 16, g32p_row07_traceSegment_033_0819_0015, g32p_row07_traceSegment_033_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 789 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 789 30 31, g32p_row07_traceSegment_033_0789_0030, g32p_row07_traceSegment_033_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_033 729 121 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 729 60 61, g32p_row07_traceSegment_033_0729_0060, g32p_row07_traceSegment_033_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 850 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 865 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 850 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 850 15 15, g32p_row07_traceSegment_033_0850_0015, g32p_row07_traceSegment_033_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 880 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 895 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 880 31 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 880 15 16, g32p_row07_traceSegment_033_0880_0015, g32p_row07_traceSegment_033_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 850 61 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 850 30 31, g32p_row07_traceSegment_033_0850_0030, g32p_row07_traceSegment_033_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 911 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 926 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 911 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 911 15 15, g32p_row07_traceSegment_033_0911_0015, g32p_row07_traceSegment_033_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 941 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 956 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 941 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 941 15 16, g32p_row07_traceSegment_033_0941_0015, g32p_row07_traceSegment_033_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 911 61 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 911 30 31, g32p_row07_traceSegment_033_0911_0030, g32p_row07_traceSegment_033_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_033 850 122 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 850 61 61, g32p_row07_traceSegment_033_0850_0061, g32p_row07_traceSegment_033_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_033 729 243 = [0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 729 121 122, g32p_row07_traceSegment_033_0729_0121, g32p_row07_traceSegment_033_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_033 486 486 = [0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 486 243 243, g32p_row07_traceSegment_033_0486_0243, g32p_row07_traceSegment_033_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_033 0 972 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 0 486 486, g32p_row07_traceSegment_033_0000_0486, g32p_row07_traceSegment_033_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 972 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 987 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 972 30 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 972 15 15, g32p_row07_traceSegment_033_0972_0015, g32p_row07_traceSegment_033_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1002 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1017 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1002 30 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1002 15 15, g32p_row07_traceSegment_033_1002_0015, g32p_row07_traceSegment_033_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_033 972 60 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 972 30 30, g32p_row07_traceSegment_033_0972_0030, g32p_row07_traceSegment_033_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1032 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1047 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1032 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1032 15 15, g32p_row07_traceSegment_033_1032_0015, g32p_row07_traceSegment_033_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1062 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1062 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1062 15 16, g32p_row07_traceSegment_033_1062_0015, g32p_row07_traceSegment_033_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1032 61 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1032 30 31, g32p_row07_traceSegment_033_1032_0030, g32p_row07_traceSegment_033_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_033 972 121 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 972 60 61, g32p_row07_traceSegment_033_0972_0060, g32p_row07_traceSegment_033_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1093 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1108 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1093 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1093 15 15, g32p_row07_traceSegment_033_1093_0015, g32p_row07_traceSegment_033_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1123 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1138 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1123 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1123 15 16, g32p_row07_traceSegment_033_1123_0015, g32p_row07_traceSegment_033_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1093 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1093 30 31, g32p_row07_traceSegment_033_1093_0030, g32p_row07_traceSegment_033_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1154 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1169 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1154 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1154 15 15, g32p_row07_traceSegment_033_1154_0015, g32p_row07_traceSegment_033_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1184 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1199 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1184 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1184 15 16, g32p_row07_traceSegment_033_1184_0015, g32p_row07_traceSegment_033_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1154 61 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1154 30 31, g32p_row07_traceSegment_033_1154_0030, g32p_row07_traceSegment_033_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_033 1093 122 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1093 61 61, g32p_row07_traceSegment_033_1093_0061, g32p_row07_traceSegment_033_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_033 972 243 = [0, 0, 33] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 972 121 122, g32p_row07_traceSegment_033_0972_0121, g32p_row07_traceSegment_033_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1215 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1230 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1215 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1215 15 15, g32p_row07_traceSegment_033_1215_0015, g32p_row07_traceSegment_033_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1245 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1260 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1245 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1245 15 15, g32p_row07_traceSegment_033_1245_0015, g32p_row07_traceSegment_033_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_033 1215 60 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1215 30 30, g32p_row07_traceSegment_033_1215_0030, g32p_row07_traceSegment_033_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1275 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1275 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1275 15 15, g32p_row07_traceSegment_033_1275_0015, g32p_row07_traceSegment_033_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1305 15 16, g32p_row07_traceSegment_033_1305_0015, g32p_row07_traceSegment_033_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1275 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1275 30 31, g32p_row07_traceSegment_033_1275_0030, g32p_row07_traceSegment_033_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_033 1215 121 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1215 60 61, g32p_row07_traceSegment_033_1215_0060, g32p_row07_traceSegment_033_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1336 15 15, g32p_row07_traceSegment_033_1336_0015, g32p_row07_traceSegment_033_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1366 15 16, g32p_row07_traceSegment_033_1366_0015, g32p_row07_traceSegment_033_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1336 30 31, g32p_row07_traceSegment_033_1336_0030, g32p_row07_traceSegment_033_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1397 15 15, g32p_row07_traceSegment_033_1397_0015, g32p_row07_traceSegment_033_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1427 15 16, g32p_row07_traceSegment_033_1427_0015, g32p_row07_traceSegment_033_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1397 30 31, g32p_row07_traceSegment_033_1397_0030, g32p_row07_traceSegment_033_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_033 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1336 61 61, g32p_row07_traceSegment_033_1336_0061, g32p_row07_traceSegment_033_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_033 1215 243 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1215 121 122, g32p_row07_traceSegment_033_1215_0121, g32p_row07_traceSegment_033_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_033 972 486 = [0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 972 243 243, g32p_row07_traceSegment_033_0972_0243, g32p_row07_traceSegment_033_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1458 15 15, g32p_row07_traceSegment_033_1458_0015, g32p_row07_traceSegment_033_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1488 15 15, g32p_row07_traceSegment_033_1488_0015, g32p_row07_traceSegment_033_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_033 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1458 30 30, g32p_row07_traceSegment_033_1458_0030, g32p_row07_traceSegment_033_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1518 15 15, g32p_row07_traceSegment_033_1518_0015, g32p_row07_traceSegment_033_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1548 15 16, g32p_row07_traceSegment_033_1548_0015, g32p_row07_traceSegment_033_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1518 30 31, g32p_row07_traceSegment_033_1518_0030, g32p_row07_traceSegment_033_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_033 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1458 60 61, g32p_row07_traceSegment_033_1458_0060, g32p_row07_traceSegment_033_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1579 15 15, g32p_row07_traceSegment_033_1579_0015, g32p_row07_traceSegment_033_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1609 15 16, g32p_row07_traceSegment_033_1609_0015, g32p_row07_traceSegment_033_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1579 30 31, g32p_row07_traceSegment_033_1579_0030, g32p_row07_traceSegment_033_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1640 15 15, g32p_row07_traceSegment_033_1640_0015, g32p_row07_traceSegment_033_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1670 15 16, g32p_row07_traceSegment_033_1670_0015, g32p_row07_traceSegment_033_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1640 30 31, g32p_row07_traceSegment_033_1640_0030, g32p_row07_traceSegment_033_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_033 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1579 61 61, g32p_row07_traceSegment_033_1579_0061, g32p_row07_traceSegment_033_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_033 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1458 121 122, g32p_row07_traceSegment_033_1458_0121, g32p_row07_traceSegment_033_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1701 15 15, g32p_row07_traceSegment_033_1701_0015, g32p_row07_traceSegment_033_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1731 15 15, g32p_row07_traceSegment_033_1731_0015, g32p_row07_traceSegment_033_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_033 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1701 30 30, g32p_row07_traceSegment_033_1701_0030, g32p_row07_traceSegment_033_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1761 15 15, g32p_row07_traceSegment_033_1761_0015, g32p_row07_traceSegment_033_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1791 15 16, g32p_row07_traceSegment_033_1791_0015, g32p_row07_traceSegment_033_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1761 30 31, g32p_row07_traceSegment_033_1761_0030, g32p_row07_traceSegment_033_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_033 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1701 60 61, g32p_row07_traceSegment_033_1701_0060, g32p_row07_traceSegment_033_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1822 15 15, g32p_row07_traceSegment_033_1822_0015, g32p_row07_traceSegment_033_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1852 15 16, g32p_row07_traceSegment_033_1852_0015, g32p_row07_traceSegment_033_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1822 30 31, g32p_row07_traceSegment_033_1822_0030, g32p_row07_traceSegment_033_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_033 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1883 15 15, g32p_row07_traceSegment_033_1883_0015, g32p_row07_traceSegment_033_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_033 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_033 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_033_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_033 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1913 15 16, g32p_row07_traceSegment_033_1913_0015, g32p_row07_traceSegment_033_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_033 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1883 30 31, g32p_row07_traceSegment_033_1883_0030, g32p_row07_traceSegment_033_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_033 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1822 61 61, g32p_row07_traceSegment_033_1822_0061, g32p_row07_traceSegment_033_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_033 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1701 121 122, g32p_row07_traceSegment_033_1701_0121, g32p_row07_traceSegment_033_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_033_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_033 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 1458 243 243, g32p_row07_traceSegment_033_1458_0243, g32p_row07_traceSegment_033_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_033 972 972 = [0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 972 486 486, g32p_row07_traceSegment_033_0972_0486, g32p_row07_traceSegment_033_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_033_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_033 0 1944 = [0, 0, 72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_033 0 972 972, g32p_row07_traceSegment_033_0000_0972, g32p_row07_traceSegment_033_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_033 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 33 = [0, 0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_033_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row07_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 13) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 13) (g32p_literalTraceValue 6 13)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_013]
  decide +kernel

theorem g32p_row07_tracePolynomial_014 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 14) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 14) (g32p_literalTraceValue 6 14)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row07_traceCoefficients_014]
  decide +kernel

theorem g32p_row07_tracePolynomial_021 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 21) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 21) (g32p_literalTraceValue 6 21)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_021]
  decide +kernel

theorem g32p_row07_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 24) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 24) (g32p_literalTraceValue 6 24)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_024]
  decide +kernel

theorem g32p_row07_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 28) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 28) (g32p_literalTraceValue 6 28)
      [1, 1, 1] [] = true := by
  rw [g32p_row07_traceCoefficients_028]
  decide +kernel

theorem g32p_row07_tracePolynomial_030 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 30) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 30) (g32p_literalTraceValue 6 30)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row07_traceCoefficients_030]
  decide +kernel

theorem g32p_row07_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 32) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 32) (g32p_literalTraceValue 6 32)
      [1, 1, 1] [27216] = true := by
  rw [g32p_row07_traceCoefficients_032]
  decide +kernel

theorem g32p_row07_tracePolynomial_033 :
    g32p_supplierTracePolynomialCheck 1944 (g32p_literalCentralizer 33) 3
      (g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 33) (g32p_literalTraceValue 6 33)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row07_traceCoefficients_033]
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

private def g32p_row07_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_034_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 0 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 0 15 15, g32p_row07_traceSegment_034_0000_0015, g32p_row07_traceSegment_034_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 30 15 15, g32p_row07_traceSegment_034_0030_0015, g32p_row07_traceSegment_034_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_034 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 0 30 30, g32p_row07_traceSegment_034_0000_0030, g32p_row07_traceSegment_034_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 75 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 60 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 60 15 15, g32p_row07_traceSegment_034_0060_0015, g32p_row07_traceSegment_034_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 90 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 105 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 90 31 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 90 15 16, g32p_row07_traceSegment_034_0090_0015, g32p_row07_traceSegment_034_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 60 61 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 60 30 31, g32p_row07_traceSegment_034_0060_0030, g32p_row07_traceSegment_034_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_034 0 121 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 0 60 61, g32p_row07_traceSegment_034_0000_0060, g32p_row07_traceSegment_034_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 136 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 121 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 121 15 15, g32p_row07_traceSegment_034_0121_0015, g32p_row07_traceSegment_034_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 151 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 151 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 151 15 16, g32p_row07_traceSegment_034_0151_0015, g32p_row07_traceSegment_034_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 121 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 121 30 31, g32p_row07_traceSegment_034_0121_0030, g32p_row07_traceSegment_034_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 182 15 15, g32p_row07_traceSegment_034_0182_0015, g32p_row07_traceSegment_034_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 212 15 16, g32p_row07_traceSegment_034_0212_0015, g32p_row07_traceSegment_034_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 182 30 31, g32p_row07_traceSegment_034_0182_0030, g32p_row07_traceSegment_034_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_034 121 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 121 61 61, g32p_row07_traceSegment_034_0121_0061, g32p_row07_traceSegment_034_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_034 0 243 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 0 121 122, g32p_row07_traceSegment_034_0000_0121, g32p_row07_traceSegment_034_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 243 15 15, g32p_row07_traceSegment_034_0243_0015, g32p_row07_traceSegment_034_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 273 15 15, g32p_row07_traceSegment_034_0273_0015, g32p_row07_traceSegment_034_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_034 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 243 30 30, g32p_row07_traceSegment_034_0243_0030, g32p_row07_traceSegment_034_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 303 15 15, g32p_row07_traceSegment_034_0303_0015, g32p_row07_traceSegment_034_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 333 15 16, g32p_row07_traceSegment_034_0333_0015, g32p_row07_traceSegment_034_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 303 30 31, g32p_row07_traceSegment_034_0303_0030, g32p_row07_traceSegment_034_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_034 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 243 60 61, g32p_row07_traceSegment_034_0243_0060, g32p_row07_traceSegment_034_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 364 15 15, g32p_row07_traceSegment_034_0364_0015, g32p_row07_traceSegment_034_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 394 15 16, g32p_row07_traceSegment_034_0394_0015, g32p_row07_traceSegment_034_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 364 30 31, g32p_row07_traceSegment_034_0364_0030, g32p_row07_traceSegment_034_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 425 15 15, g32p_row07_traceSegment_034_0425_0015, g32p_row07_traceSegment_034_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 455 15 16, g32p_row07_traceSegment_034_0455_0015, g32p_row07_traceSegment_034_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 425 30 31, g32p_row07_traceSegment_034_0425_0030, g32p_row07_traceSegment_034_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_034 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 364 61 61, g32p_row07_traceSegment_034_0364_0061, g32p_row07_traceSegment_034_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_034 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 243 121 122, g32p_row07_traceSegment_034_0243_0121, g32p_row07_traceSegment_034_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_034 0 486 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 0 243 243, g32p_row07_traceSegment_034_0000_0243, g32p_row07_traceSegment_034_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 486 15 15, g32p_row07_traceSegment_034_0486_0015, g32p_row07_traceSegment_034_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 516 15 15, g32p_row07_traceSegment_034_0516_0015, g32p_row07_traceSegment_034_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_034 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 486 30 30, g32p_row07_traceSegment_034_0486_0030, g32p_row07_traceSegment_034_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 546 15 15, g32p_row07_traceSegment_034_0546_0015, g32p_row07_traceSegment_034_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 576 15 16, g32p_row07_traceSegment_034_0576_0015, g32p_row07_traceSegment_034_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 546 30 31, g32p_row07_traceSegment_034_0546_0030, g32p_row07_traceSegment_034_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_034 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 486 60 61, g32p_row07_traceSegment_034_0486_0060, g32p_row07_traceSegment_034_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 607 15 15, g32p_row07_traceSegment_034_0607_0015, g32p_row07_traceSegment_034_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 637 15 16, g32p_row07_traceSegment_034_0637_0015, g32p_row07_traceSegment_034_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 607 30 31, g32p_row07_traceSegment_034_0607_0030, g32p_row07_traceSegment_034_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 668 15 15, g32p_row07_traceSegment_034_0668_0015, g32p_row07_traceSegment_034_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 698 15 16, g32p_row07_traceSegment_034_0698_0015, g32p_row07_traceSegment_034_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 668 30 31, g32p_row07_traceSegment_034_0668_0030, g32p_row07_traceSegment_034_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_034 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 607 61 61, g32p_row07_traceSegment_034_0607_0061, g32p_row07_traceSegment_034_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_034 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 486 121 122, g32p_row07_traceSegment_034_0486_0121, g32p_row07_traceSegment_034_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 729 15 15, g32p_row07_traceSegment_034_0729_0015, g32p_row07_traceSegment_034_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 774 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 759 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 759 15 15, g32p_row07_traceSegment_034_0759_0015, g32p_row07_traceSegment_034_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_034 729 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 729 30 30, g32p_row07_traceSegment_034_0729_0030, g32p_row07_traceSegment_034_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 789 15 15, g32p_row07_traceSegment_034_0789_0015, g32p_row07_traceSegment_034_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 819 15 16, g32p_row07_traceSegment_034_0819_0015, g32p_row07_traceSegment_034_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 789 30 31, g32p_row07_traceSegment_034_0789_0030, g32p_row07_traceSegment_034_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_034 729 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 729 60 61, g32p_row07_traceSegment_034_0729_0060, g32p_row07_traceSegment_034_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 850 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 850 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 850 15 15, g32p_row07_traceSegment_034_0850_0015, g32p_row07_traceSegment_034_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 880 15 16, g32p_row07_traceSegment_034_0880_0015, g32p_row07_traceSegment_034_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 850 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 850 30 31, g32p_row07_traceSegment_034_0850_0030, g32p_row07_traceSegment_034_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 911 15 15, g32p_row07_traceSegment_034_0911_0015, g32p_row07_traceSegment_034_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 941 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 941 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 941 15 16, g32p_row07_traceSegment_034_0941_0015, g32p_row07_traceSegment_034_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 911 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 911 30 31, g32p_row07_traceSegment_034_0911_0030, g32p_row07_traceSegment_034_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_034 850 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 850 61 61, g32p_row07_traceSegment_034_0850_0061, g32p_row07_traceSegment_034_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_034 729 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 729 121 122, g32p_row07_traceSegment_034_0729_0121, g32p_row07_traceSegment_034_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_034 486 486 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 486 243 243, g32p_row07_traceSegment_034_0486_0243, g32p_row07_traceSegment_034_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_034 0 972 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 0 486 486, g32p_row07_traceSegment_034_0000_0486, g32p_row07_traceSegment_034_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 972 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 972 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 972 15 15, g32p_row07_traceSegment_034_0972_0015, g32p_row07_traceSegment_034_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1017 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1002 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1002 15 15, g32p_row07_traceSegment_034_1002_0015, g32p_row07_traceSegment_034_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_034 972 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 972 30 30, g32p_row07_traceSegment_034_0972_0030, g32p_row07_traceSegment_034_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1032 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1032 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1032 15 15, g32p_row07_traceSegment_034_1032_0015, g32p_row07_traceSegment_034_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1062 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1077 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1062 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1062 15 16, g32p_row07_traceSegment_034_1062_0015, g32p_row07_traceSegment_034_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1032 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1032 30 31, g32p_row07_traceSegment_034_1032_0030, g32p_row07_traceSegment_034_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_034 972 121 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 972 60 61, g32p_row07_traceSegment_034_0972_0060, g32p_row07_traceSegment_034_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1093 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1108 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1093 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1093 15 15, g32p_row07_traceSegment_034_1093_0015, g32p_row07_traceSegment_034_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1123 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1123 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1123 15 16, g32p_row07_traceSegment_034_1123_0015, g32p_row07_traceSegment_034_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1093 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1093 30 31, g32p_row07_traceSegment_034_1093_0030, g32p_row07_traceSegment_034_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1154 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1169 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1154 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1154 15 15, g32p_row07_traceSegment_034_1154_0015, g32p_row07_traceSegment_034_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1184 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1199 16 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1184 31 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1184 15 16, g32p_row07_traceSegment_034_1184_0015, g32p_row07_traceSegment_034_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1154 61 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1154 30 31, g32p_row07_traceSegment_034_1154_0030, g32p_row07_traceSegment_034_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_034 1093 122 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1093 61 61, g32p_row07_traceSegment_034_1093_0061, g32p_row07_traceSegment_034_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_034 972 243 = [0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 972 121 122, g32p_row07_traceSegment_034_0972_0121, g32p_row07_traceSegment_034_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1215 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1230 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1215 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1215 15 15, g32p_row07_traceSegment_034_1215_0015, g32p_row07_traceSegment_034_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1245 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1260 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1245 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1245 15 15, g32p_row07_traceSegment_034_1245_0015, g32p_row07_traceSegment_034_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_034 1215 60 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1215 30 30, g32p_row07_traceSegment_034_1215_0030, g32p_row07_traceSegment_034_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1275 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1275 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1275 15 15, g32p_row07_traceSegment_034_1275_0015, g32p_row07_traceSegment_034_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1305 15 16, g32p_row07_traceSegment_034_1305_0015, g32p_row07_traceSegment_034_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1275 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1275 30 31, g32p_row07_traceSegment_034_1275_0030, g32p_row07_traceSegment_034_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_034 1215 121 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1215 60 61, g32p_row07_traceSegment_034_1215_0060, g32p_row07_traceSegment_034_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1336 15 15, g32p_row07_traceSegment_034_1336_0015, g32p_row07_traceSegment_034_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1366 15 16, g32p_row07_traceSegment_034_1366_0015, g32p_row07_traceSegment_034_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1336 30 31, g32p_row07_traceSegment_034_1336_0030, g32p_row07_traceSegment_034_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1397 15 15, g32p_row07_traceSegment_034_1397_0015, g32p_row07_traceSegment_034_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1427 15 16, g32p_row07_traceSegment_034_1427_0015, g32p_row07_traceSegment_034_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1397 30 31, g32p_row07_traceSegment_034_1397_0030, g32p_row07_traceSegment_034_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_034 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1336 61 61, g32p_row07_traceSegment_034_1336_0061, g32p_row07_traceSegment_034_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_034 1215 243 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1215 121 122, g32p_row07_traceSegment_034_1215_0121, g32p_row07_traceSegment_034_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_034 972 486 = [0, 0, 37] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 972 243 243, g32p_row07_traceSegment_034_0972_0243, g32p_row07_traceSegment_034_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1458 15 15, g32p_row07_traceSegment_034_1458_0015, g32p_row07_traceSegment_034_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1488 15 15, g32p_row07_traceSegment_034_1488_0015, g32p_row07_traceSegment_034_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_034 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1458 30 30, g32p_row07_traceSegment_034_1458_0030, g32p_row07_traceSegment_034_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1518 15 15, g32p_row07_traceSegment_034_1518_0015, g32p_row07_traceSegment_034_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1548 15 16, g32p_row07_traceSegment_034_1548_0015, g32p_row07_traceSegment_034_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1518 30 31, g32p_row07_traceSegment_034_1518_0030, g32p_row07_traceSegment_034_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_034 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1458 60 61, g32p_row07_traceSegment_034_1458_0060, g32p_row07_traceSegment_034_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1579 15 15, g32p_row07_traceSegment_034_1579_0015, g32p_row07_traceSegment_034_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1609 15 16, g32p_row07_traceSegment_034_1609_0015, g32p_row07_traceSegment_034_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1579 30 31, g32p_row07_traceSegment_034_1579_0030, g32p_row07_traceSegment_034_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1640 15 15, g32p_row07_traceSegment_034_1640_0015, g32p_row07_traceSegment_034_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1670 15 16, g32p_row07_traceSegment_034_1670_0015, g32p_row07_traceSegment_034_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1640 30 31, g32p_row07_traceSegment_034_1640_0030, g32p_row07_traceSegment_034_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_034 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1579 61 61, g32p_row07_traceSegment_034_1579_0061, g32p_row07_traceSegment_034_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_034 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1458 121 122, g32p_row07_traceSegment_034_1458_0121, g32p_row07_traceSegment_034_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1701 15 15, g32p_row07_traceSegment_034_1701_0015, g32p_row07_traceSegment_034_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1731 15 15, g32p_row07_traceSegment_034_1731_0015, g32p_row07_traceSegment_034_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_034 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1701 30 30, g32p_row07_traceSegment_034_1701_0030, g32p_row07_traceSegment_034_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1761 15 15, g32p_row07_traceSegment_034_1761_0015, g32p_row07_traceSegment_034_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1791 15 16, g32p_row07_traceSegment_034_1791_0015, g32p_row07_traceSegment_034_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1761 30 31, g32p_row07_traceSegment_034_1761_0030, g32p_row07_traceSegment_034_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_034 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1701 60 61, g32p_row07_traceSegment_034_1701_0060, g32p_row07_traceSegment_034_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1822 15 15, g32p_row07_traceSegment_034_1822_0015, g32p_row07_traceSegment_034_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1852 15 16, g32p_row07_traceSegment_034_1852_0015, g32p_row07_traceSegment_034_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1822 30 31, g32p_row07_traceSegment_034_1822_0030, g32p_row07_traceSegment_034_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_034 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1883 15 15, g32p_row07_traceSegment_034_1883_0015, g32p_row07_traceSegment_034_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_034 1913 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_034 1928 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_034_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_034 1913 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1913 15 16, g32p_row07_traceSegment_034_1913_0015, g32p_row07_traceSegment_034_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_034 1883 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1883 30 31, g32p_row07_traceSegment_034_1883_0030, g32p_row07_traceSegment_034_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_034 1822 122 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1822 61 61, g32p_row07_traceSegment_034_1822_0061, g32p_row07_traceSegment_034_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_034 1701 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1701 121 122, g32p_row07_traceSegment_034_1701_0121, g32p_row07_traceSegment_034_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_034_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_034 1458 486 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 1458 243 243, g32p_row07_traceSegment_034_1458_0243, g32p_row07_traceSegment_034_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_034 972 972 = [0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 972 486 486, g32p_row07_traceSegment_034_0972_0486, g32p_row07_traceSegment_034_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_034_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_034 0 1944 = [0, 0, 54] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_034 0 972 972, g32p_row07_traceSegment_034_0000_0972, g32p_row07_traceSegment_034_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 34 = [0, 0, 54] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_034_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_035 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 35 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_035_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 0 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 0 15 15, g32p_row07_traceSegment_035_0000_0015, g32p_row07_traceSegment_035_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 30 15 15, g32p_row07_traceSegment_035_0030_0015, g32p_row07_traceSegment_035_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_035 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 0 30 30, g32p_row07_traceSegment_035_0000_0030, g32p_row07_traceSegment_035_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 75 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 60 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 60 15 15, g32p_row07_traceSegment_035_0060_0015, g32p_row07_traceSegment_035_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 90 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 105 16 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 90 31 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 90 15 16, g32p_row07_traceSegment_035_0090_0015, g32p_row07_traceSegment_035_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 60 61 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 60 30 31, g32p_row07_traceSegment_035_0060_0030, g32p_row07_traceSegment_035_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_035 0 121 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 0 60 61, g32p_row07_traceSegment_035_0000_0060, g32p_row07_traceSegment_035_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 121 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 136 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 121 30 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 121 15 15, g32p_row07_traceSegment_035_0121_0015, g32p_row07_traceSegment_035_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 151 15 16, g32p_row07_traceSegment_035_0151_0015, g32p_row07_traceSegment_035_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 121 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 121 30 31, g32p_row07_traceSegment_035_0121_0030, g32p_row07_traceSegment_035_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 182 15 15, g32p_row07_traceSegment_035_0182_0015, g32p_row07_traceSegment_035_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 212 15 16, g32p_row07_traceSegment_035_0212_0015, g32p_row07_traceSegment_035_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 182 30 31, g32p_row07_traceSegment_035_0182_0030, g32p_row07_traceSegment_035_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_035 121 122 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 121 61 61, g32p_row07_traceSegment_035_0121_0061, g32p_row07_traceSegment_035_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_035 0 243 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 0 121 122, g32p_row07_traceSegment_035_0000_0121, g32p_row07_traceSegment_035_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 243 15 15, g32p_row07_traceSegment_035_0243_0015, g32p_row07_traceSegment_035_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 273 15 15, g32p_row07_traceSegment_035_0273_0015, g32p_row07_traceSegment_035_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_035 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 243 30 30, g32p_row07_traceSegment_035_0243_0030, g32p_row07_traceSegment_035_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 303 15 15, g32p_row07_traceSegment_035_0303_0015, g32p_row07_traceSegment_035_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 333 15 16, g32p_row07_traceSegment_035_0333_0015, g32p_row07_traceSegment_035_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 303 30 31, g32p_row07_traceSegment_035_0303_0030, g32p_row07_traceSegment_035_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_035 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 243 60 61, g32p_row07_traceSegment_035_0243_0060, g32p_row07_traceSegment_035_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 364 15 15, g32p_row07_traceSegment_035_0364_0015, g32p_row07_traceSegment_035_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 394 15 16, g32p_row07_traceSegment_035_0394_0015, g32p_row07_traceSegment_035_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 364 30 31, g32p_row07_traceSegment_035_0364_0030, g32p_row07_traceSegment_035_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 425 15 15, g32p_row07_traceSegment_035_0425_0015, g32p_row07_traceSegment_035_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 455 15 16, g32p_row07_traceSegment_035_0455_0015, g32p_row07_traceSegment_035_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 425 30 31, g32p_row07_traceSegment_035_0425_0030, g32p_row07_traceSegment_035_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_035 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 364 61 61, g32p_row07_traceSegment_035_0364_0061, g32p_row07_traceSegment_035_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_035 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 243 121 122, g32p_row07_traceSegment_035_0243_0121, g32p_row07_traceSegment_035_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_035 0 486 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 0 243 243, g32p_row07_traceSegment_035_0000_0243, g32p_row07_traceSegment_035_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 486 15 15, g32p_row07_traceSegment_035_0486_0015, g32p_row07_traceSegment_035_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 516 15 15, g32p_row07_traceSegment_035_0516_0015, g32p_row07_traceSegment_035_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_035 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 486 30 30, g32p_row07_traceSegment_035_0486_0030, g32p_row07_traceSegment_035_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 546 15 15, g32p_row07_traceSegment_035_0546_0015, g32p_row07_traceSegment_035_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 576 15 16, g32p_row07_traceSegment_035_0576_0015, g32p_row07_traceSegment_035_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 546 30 31, g32p_row07_traceSegment_035_0546_0030, g32p_row07_traceSegment_035_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_035 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 486 60 61, g32p_row07_traceSegment_035_0486_0060, g32p_row07_traceSegment_035_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 607 15 15, g32p_row07_traceSegment_035_0607_0015, g32p_row07_traceSegment_035_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 637 15 16, g32p_row07_traceSegment_035_0637_0015, g32p_row07_traceSegment_035_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 607 30 31, g32p_row07_traceSegment_035_0607_0030, g32p_row07_traceSegment_035_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 668 15 15, g32p_row07_traceSegment_035_0668_0015, g32p_row07_traceSegment_035_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 698 15 16, g32p_row07_traceSegment_035_0698_0015, g32p_row07_traceSegment_035_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 668 30 31, g32p_row07_traceSegment_035_0668_0030, g32p_row07_traceSegment_035_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_035 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 607 61 61, g32p_row07_traceSegment_035_0607_0061, g32p_row07_traceSegment_035_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_035 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 486 121 122, g32p_row07_traceSegment_035_0486_0121, g32p_row07_traceSegment_035_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 729 15 15, g32p_row07_traceSegment_035_0729_0015, g32p_row07_traceSegment_035_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 774 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 759 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 759 15 15, g32p_row07_traceSegment_035_0759_0015, g32p_row07_traceSegment_035_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_035 729 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 729 30 30, g32p_row07_traceSegment_035_0729_0030, g32p_row07_traceSegment_035_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 789 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 804 15 = [0, 0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 789 30 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 789 15 15, g32p_row07_traceSegment_035_0789_0015, g32p_row07_traceSegment_035_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 819 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 834 16 = [0, 0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 819 31 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 819 15 16, g32p_row07_traceSegment_035_0819_0015, g32p_row07_traceSegment_035_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 789 61 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 789 30 31, g32p_row07_traceSegment_035_0789_0030, g32p_row07_traceSegment_035_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_035 729 121 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 729 60 61, g32p_row07_traceSegment_035_0729_0060, g32p_row07_traceSegment_035_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 850 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 865 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 850 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 850 15 15, g32p_row07_traceSegment_035_0850_0015, g32p_row07_traceSegment_035_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 880 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 895 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 880 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 880 15 16, g32p_row07_traceSegment_035_0880_0015, g32p_row07_traceSegment_035_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 850 61 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 850 30 31, g32p_row07_traceSegment_035_0850_0030, g32p_row07_traceSegment_035_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 911 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 926 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 911 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 911 15 15, g32p_row07_traceSegment_035_0911_0015, g32p_row07_traceSegment_035_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 956 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 941 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 941 15 16, g32p_row07_traceSegment_035_0941_0015, g32p_row07_traceSegment_035_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 911 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 911 30 31, g32p_row07_traceSegment_035_0911_0030, g32p_row07_traceSegment_035_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_035 850 122 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 850 61 61, g32p_row07_traceSegment_035_0850_0061, g32p_row07_traceSegment_035_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_035 729 243 = [0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 729 121 122, g32p_row07_traceSegment_035_0729_0121, g32p_row07_traceSegment_035_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_035 486 486 = [0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 486 243 243, g32p_row07_traceSegment_035_0486_0243, g32p_row07_traceSegment_035_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_035 0 972 = [0, 0, 46] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 0 486 486, g32p_row07_traceSegment_035_0000_0486, g32p_row07_traceSegment_035_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 972 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 972 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 972 15 15, g32p_row07_traceSegment_035_0972_0015, g32p_row07_traceSegment_035_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1002 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1017 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1002 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1002 15 15, g32p_row07_traceSegment_035_1002_0015, g32p_row07_traceSegment_035_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_035 972 60 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 972 30 30, g32p_row07_traceSegment_035_0972_0030, g32p_row07_traceSegment_035_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1032 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1047 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1032 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1032 15 15, g32p_row07_traceSegment_035_1032_0015, g32p_row07_traceSegment_035_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1062 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1077 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1062 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1062 15 16, g32p_row07_traceSegment_035_1062_0015, g32p_row07_traceSegment_035_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1032 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1032 30 31, g32p_row07_traceSegment_035_1032_0030, g32p_row07_traceSegment_035_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_035 972 121 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 972 60 61, g32p_row07_traceSegment_035_0972_0060, g32p_row07_traceSegment_035_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1093 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1108 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1093 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1093 15 15, g32p_row07_traceSegment_035_1093_0015, g32p_row07_traceSegment_035_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1123 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1138 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1123 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1123 15 16, g32p_row07_traceSegment_035_1123_0015, g32p_row07_traceSegment_035_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1093 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1093 30 31, g32p_row07_traceSegment_035_1093_0030, g32p_row07_traceSegment_035_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1154 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1169 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1154 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1154 15 15, g32p_row07_traceSegment_035_1154_0015, g32p_row07_traceSegment_035_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1184 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1199 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1184 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1184 15 16, g32p_row07_traceSegment_035_1184_0015, g32p_row07_traceSegment_035_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1154 61 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1154 30 31, g32p_row07_traceSegment_035_1154_0030, g32p_row07_traceSegment_035_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_035 1093 122 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1093 61 61, g32p_row07_traceSegment_035_1093_0061, g32p_row07_traceSegment_035_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_035 972 243 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 972 121 122, g32p_row07_traceSegment_035_0972_0121, g32p_row07_traceSegment_035_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1215 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1230 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1215 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1215 15 15, g32p_row07_traceSegment_035_1215_0015, g32p_row07_traceSegment_035_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1245 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1260 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1245 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1245 15 15, g32p_row07_traceSegment_035_1245_0015, g32p_row07_traceSegment_035_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_035 1215 60 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1215 30 30, g32p_row07_traceSegment_035_1215_0030, g32p_row07_traceSegment_035_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1275 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1275 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1275 15 15, g32p_row07_traceSegment_035_1275_0015, g32p_row07_traceSegment_035_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1305 15 16, g32p_row07_traceSegment_035_1305_0015, g32p_row07_traceSegment_035_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1275 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1275 30 31, g32p_row07_traceSegment_035_1275_0030, g32p_row07_traceSegment_035_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_035 1215 121 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1215 60 61, g32p_row07_traceSegment_035_1215_0060, g32p_row07_traceSegment_035_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1336 15 15, g32p_row07_traceSegment_035_1336_0015, g32p_row07_traceSegment_035_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1366 15 16, g32p_row07_traceSegment_035_1366_0015, g32p_row07_traceSegment_035_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1336 30 31, g32p_row07_traceSegment_035_1336_0030, g32p_row07_traceSegment_035_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1397 15 15, g32p_row07_traceSegment_035_1397_0015, g32p_row07_traceSegment_035_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1427 15 16, g32p_row07_traceSegment_035_1427_0015, g32p_row07_traceSegment_035_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1397 30 31, g32p_row07_traceSegment_035_1397_0030, g32p_row07_traceSegment_035_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_035 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1336 61 61, g32p_row07_traceSegment_035_1336_0061, g32p_row07_traceSegment_035_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_035 1215 243 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1215 121 122, g32p_row07_traceSegment_035_1215_0121, g32p_row07_traceSegment_035_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_035 972 486 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 972 243 243, g32p_row07_traceSegment_035_0972_0243, g32p_row07_traceSegment_035_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1458 15 15, g32p_row07_traceSegment_035_1458_0015, g32p_row07_traceSegment_035_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1488 15 15, g32p_row07_traceSegment_035_1488_0015, g32p_row07_traceSegment_035_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_035 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1458 30 30, g32p_row07_traceSegment_035_1458_0030, g32p_row07_traceSegment_035_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1518 15 15, g32p_row07_traceSegment_035_1518_0015, g32p_row07_traceSegment_035_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1548 15 16, g32p_row07_traceSegment_035_1548_0015, g32p_row07_traceSegment_035_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1518 30 31, g32p_row07_traceSegment_035_1518_0030, g32p_row07_traceSegment_035_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_035 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1458 60 61, g32p_row07_traceSegment_035_1458_0060, g32p_row07_traceSegment_035_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1579 15 15, g32p_row07_traceSegment_035_1579_0015, g32p_row07_traceSegment_035_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1609 15 16, g32p_row07_traceSegment_035_1609_0015, g32p_row07_traceSegment_035_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1579 30 31, g32p_row07_traceSegment_035_1579_0030, g32p_row07_traceSegment_035_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1640 15 15, g32p_row07_traceSegment_035_1640_0015, g32p_row07_traceSegment_035_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1670 15 16, g32p_row07_traceSegment_035_1670_0015, g32p_row07_traceSegment_035_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1640 30 31, g32p_row07_traceSegment_035_1640_0030, g32p_row07_traceSegment_035_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_035 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1579 61 61, g32p_row07_traceSegment_035_1579_0061, g32p_row07_traceSegment_035_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_035 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1458 121 122, g32p_row07_traceSegment_035_1458_0121, g32p_row07_traceSegment_035_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1701 15 15, g32p_row07_traceSegment_035_1701_0015, g32p_row07_traceSegment_035_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1731 15 15, g32p_row07_traceSegment_035_1731_0015, g32p_row07_traceSegment_035_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_035 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1701 30 30, g32p_row07_traceSegment_035_1701_0030, g32p_row07_traceSegment_035_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1761 15 15, g32p_row07_traceSegment_035_1761_0015, g32p_row07_traceSegment_035_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1791 15 16, g32p_row07_traceSegment_035_1791_0015, g32p_row07_traceSegment_035_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1761 30 31, g32p_row07_traceSegment_035_1761_0030, g32p_row07_traceSegment_035_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_035 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1701 60 61, g32p_row07_traceSegment_035_1701_0060, g32p_row07_traceSegment_035_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1822 15 15, g32p_row07_traceSegment_035_1822_0015, g32p_row07_traceSegment_035_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1852 15 16, g32p_row07_traceSegment_035_1852_0015, g32p_row07_traceSegment_035_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1822 30 31, g32p_row07_traceSegment_035_1822_0030, g32p_row07_traceSegment_035_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_035 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1883 15 15, g32p_row07_traceSegment_035_1883_0015, g32p_row07_traceSegment_035_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_035 1913 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_035 1928 16 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_035_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_035 1913 31 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1913 15 16, g32p_row07_traceSegment_035_1913_0015, g32p_row07_traceSegment_035_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_035 1883 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1883 30 31, g32p_row07_traceSegment_035_1883_0030, g32p_row07_traceSegment_035_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_035 1822 122 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1822 61 61, g32p_row07_traceSegment_035_1822_0061, g32p_row07_traceSegment_035_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_035 1701 243 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1701 121 122, g32p_row07_traceSegment_035_1701_0121, g32p_row07_traceSegment_035_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_035_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_035 1458 486 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 1458 243 243, g32p_row07_traceSegment_035_1458_0243, g32p_row07_traceSegment_035_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_035 972 972 = [0, 0, 38] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 972 486 486, g32p_row07_traceSegment_035_0972_0486, g32p_row07_traceSegment_035_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_035_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_035 0 1944 = [0, 0, 84] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_035 0 972 972, g32p_row07_traceSegment_035_0000_0972, g32p_row07_traceSegment_035_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 35 = [0, 0, 84] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_035_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_036 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 36 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_036_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 0 15 15, g32p_row07_traceSegment_036_0000_0015, g32p_row07_traceSegment_036_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 30 15 15, g32p_row07_traceSegment_036_0030_0015, g32p_row07_traceSegment_036_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_036 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 0 30 30, g32p_row07_traceSegment_036_0000_0030, g32p_row07_traceSegment_036_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 75 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 60 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 60 15 15, g32p_row07_traceSegment_036_0060_0015, g32p_row07_traceSegment_036_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 105 16 = [0, 0, 6] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 90 31 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 90 15 16, g32p_row07_traceSegment_036_0090_0015, g32p_row07_traceSegment_036_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 60 61 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 60 30 31, g32p_row07_traceSegment_036_0060_0030, g32p_row07_traceSegment_036_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_036 0 121 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 0 60 61, g32p_row07_traceSegment_036_0000_0060, g32p_row07_traceSegment_036_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 121 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 136 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 121 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 121 15 15, g32p_row07_traceSegment_036_0121_0015, g32p_row07_traceSegment_036_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 151 15 16, g32p_row07_traceSegment_036_0151_0015, g32p_row07_traceSegment_036_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 121 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 121 30 31, g32p_row07_traceSegment_036_0121_0030, g32p_row07_traceSegment_036_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 182 15 15, g32p_row07_traceSegment_036_0182_0015, g32p_row07_traceSegment_036_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 212 15 16, g32p_row07_traceSegment_036_0212_0015, g32p_row07_traceSegment_036_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 182 30 31, g32p_row07_traceSegment_036_0182_0030, g32p_row07_traceSegment_036_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_036 121 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 121 61 61, g32p_row07_traceSegment_036_0121_0061, g32p_row07_traceSegment_036_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_036 0 243 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 0 121 122, g32p_row07_traceSegment_036_0000_0121, g32p_row07_traceSegment_036_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 243 15 15, g32p_row07_traceSegment_036_0243_0015, g32p_row07_traceSegment_036_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 273 15 15, g32p_row07_traceSegment_036_0273_0015, g32p_row07_traceSegment_036_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_036 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 243 30 30, g32p_row07_traceSegment_036_0243_0030, g32p_row07_traceSegment_036_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 303 15 15, g32p_row07_traceSegment_036_0303_0015, g32p_row07_traceSegment_036_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 333 15 16, g32p_row07_traceSegment_036_0333_0015, g32p_row07_traceSegment_036_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 303 30 31, g32p_row07_traceSegment_036_0303_0030, g32p_row07_traceSegment_036_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_036 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 243 60 61, g32p_row07_traceSegment_036_0243_0060, g32p_row07_traceSegment_036_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 364 15 15, g32p_row07_traceSegment_036_0364_0015, g32p_row07_traceSegment_036_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 394 15 16, g32p_row07_traceSegment_036_0394_0015, g32p_row07_traceSegment_036_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 364 30 31, g32p_row07_traceSegment_036_0364_0030, g32p_row07_traceSegment_036_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 425 15 15, g32p_row07_traceSegment_036_0425_0015, g32p_row07_traceSegment_036_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 455 15 16, g32p_row07_traceSegment_036_0455_0015, g32p_row07_traceSegment_036_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 425 30 31, g32p_row07_traceSegment_036_0425_0030, g32p_row07_traceSegment_036_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_036 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 364 61 61, g32p_row07_traceSegment_036_0364_0061, g32p_row07_traceSegment_036_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_036 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 243 121 122, g32p_row07_traceSegment_036_0243_0121, g32p_row07_traceSegment_036_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_036 0 486 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 0 243 243, g32p_row07_traceSegment_036_0000_0243, g32p_row07_traceSegment_036_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 486 15 15, g32p_row07_traceSegment_036_0486_0015, g32p_row07_traceSegment_036_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 516 15 15, g32p_row07_traceSegment_036_0516_0015, g32p_row07_traceSegment_036_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_036 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 486 30 30, g32p_row07_traceSegment_036_0486_0030, g32p_row07_traceSegment_036_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 546 15 15, g32p_row07_traceSegment_036_0546_0015, g32p_row07_traceSegment_036_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 576 15 16, g32p_row07_traceSegment_036_0576_0015, g32p_row07_traceSegment_036_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 546 30 31, g32p_row07_traceSegment_036_0546_0030, g32p_row07_traceSegment_036_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_036 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 486 60 61, g32p_row07_traceSegment_036_0486_0060, g32p_row07_traceSegment_036_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 607 15 15, g32p_row07_traceSegment_036_0607_0015, g32p_row07_traceSegment_036_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 637 15 16, g32p_row07_traceSegment_036_0637_0015, g32p_row07_traceSegment_036_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 607 30 31, g32p_row07_traceSegment_036_0607_0030, g32p_row07_traceSegment_036_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 668 15 15, g32p_row07_traceSegment_036_0668_0015, g32p_row07_traceSegment_036_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 698 15 16, g32p_row07_traceSegment_036_0698_0015, g32p_row07_traceSegment_036_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 668 30 31, g32p_row07_traceSegment_036_0668_0030, g32p_row07_traceSegment_036_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_036 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 607 61 61, g32p_row07_traceSegment_036_0607_0061, g32p_row07_traceSegment_036_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_036 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 486 121 122, g32p_row07_traceSegment_036_0486_0121, g32p_row07_traceSegment_036_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 729 15 15, g32p_row07_traceSegment_036_0729_0015, g32p_row07_traceSegment_036_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 774 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 759 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 759 15 15, g32p_row07_traceSegment_036_0759_0015, g32p_row07_traceSegment_036_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_036 729 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 729 30 30, g32p_row07_traceSegment_036_0729_0030, g32p_row07_traceSegment_036_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 789 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 804 15 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 789 30 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 789 15 15, g32p_row07_traceSegment_036_0789_0015, g32p_row07_traceSegment_036_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 819 15 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 834 16 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 819 31 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 819 15 16, g32p_row07_traceSegment_036_0819_0015, g32p_row07_traceSegment_036_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 789 61 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 789 30 31, g32p_row07_traceSegment_036_0789_0030, g32p_row07_traceSegment_036_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_036 729 121 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 729 60 61, g32p_row07_traceSegment_036_0729_0060, g32p_row07_traceSegment_036_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 850 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 865 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 850 30 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 850 15 15, g32p_row07_traceSegment_036_0850_0015, g32p_row07_traceSegment_036_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 880 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 895 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 880 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 880 15 16, g32p_row07_traceSegment_036_0880_0015, g32p_row07_traceSegment_036_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 850 61 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 850 30 31, g32p_row07_traceSegment_036_0850_0030, g32p_row07_traceSegment_036_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 911 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 926 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 911 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 911 15 15, g32p_row07_traceSegment_036_0911_0015, g32p_row07_traceSegment_036_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 941 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 956 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 941 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 941 15 16, g32p_row07_traceSegment_036_0941_0015, g32p_row07_traceSegment_036_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 911 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 911 30 31, g32p_row07_traceSegment_036_0911_0030, g32p_row07_traceSegment_036_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_036 850 122 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 850 61 61, g32p_row07_traceSegment_036_0850_0061, g32p_row07_traceSegment_036_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_036 729 243 = [0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 729 121 122, g32p_row07_traceSegment_036_0729_0121, g32p_row07_traceSegment_036_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_036 486 486 = [0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 486 243 243, g32p_row07_traceSegment_036_0486_0243, g32p_row07_traceSegment_036_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_036 0 972 = [0, 0, 43] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 0 486 486, g32p_row07_traceSegment_036_0000_0486, g32p_row07_traceSegment_036_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 972 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 972 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 972 15 15, g32p_row07_traceSegment_036_0972_0015, g32p_row07_traceSegment_036_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1002 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1017 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1002 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1002 15 15, g32p_row07_traceSegment_036_1002_0015, g32p_row07_traceSegment_036_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_036 972 60 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 972 30 30, g32p_row07_traceSegment_036_0972_0030, g32p_row07_traceSegment_036_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1032 15 15, g32p_row07_traceSegment_036_1032_0015, g32p_row07_traceSegment_036_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1062 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1077 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1062 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1062 15 16, g32p_row07_traceSegment_036_1062_0015, g32p_row07_traceSegment_036_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1032 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1032 30 31, g32p_row07_traceSegment_036_1032_0030, g32p_row07_traceSegment_036_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_036 972 121 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 972 60 61, g32p_row07_traceSegment_036_0972_0060, g32p_row07_traceSegment_036_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1093 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1108 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1093 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1093 15 15, g32p_row07_traceSegment_036_1093_0015, g32p_row07_traceSegment_036_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1138 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1123 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1123 15 16, g32p_row07_traceSegment_036_1123_0015, g32p_row07_traceSegment_036_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1093 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1093 30 31, g32p_row07_traceSegment_036_1093_0030, g32p_row07_traceSegment_036_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1154 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1169 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1154 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1154 15 15, g32p_row07_traceSegment_036_1154_0015, g32p_row07_traceSegment_036_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1199 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1184 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1184 15 16, g32p_row07_traceSegment_036_1184_0015, g32p_row07_traceSegment_036_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1154 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1154 30 31, g32p_row07_traceSegment_036_1154_0030, g32p_row07_traceSegment_036_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_036 1093 122 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1093 61 61, g32p_row07_traceSegment_036_1093_0061, g32p_row07_traceSegment_036_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_036 972 243 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 972 121 122, g32p_row07_traceSegment_036_0972_0121, g32p_row07_traceSegment_036_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1215 15 15, g32p_row07_traceSegment_036_1215_0015, g32p_row07_traceSegment_036_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1245 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1260 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1245 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1245 15 15, g32p_row07_traceSegment_036_1245_0015, g32p_row07_traceSegment_036_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_036 1215 60 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1215 30 30, g32p_row07_traceSegment_036_1215_0030, g32p_row07_traceSegment_036_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1275 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1275 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1275 15 15, g32p_row07_traceSegment_036_1275_0015, g32p_row07_traceSegment_036_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1305 15 16, g32p_row07_traceSegment_036_1305_0015, g32p_row07_traceSegment_036_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1275 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1275 30 31, g32p_row07_traceSegment_036_1275_0030, g32p_row07_traceSegment_036_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_036 1215 121 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1215 60 61, g32p_row07_traceSegment_036_1215_0060, g32p_row07_traceSegment_036_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1336 15 15, g32p_row07_traceSegment_036_1336_0015, g32p_row07_traceSegment_036_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1366 15 16, g32p_row07_traceSegment_036_1366_0015, g32p_row07_traceSegment_036_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1336 30 31, g32p_row07_traceSegment_036_1336_0030, g32p_row07_traceSegment_036_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1397 15 15, g32p_row07_traceSegment_036_1397_0015, g32p_row07_traceSegment_036_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1427 15 16, g32p_row07_traceSegment_036_1427_0015, g32p_row07_traceSegment_036_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1397 30 31, g32p_row07_traceSegment_036_1397_0030, g32p_row07_traceSegment_036_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_036 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1336 61 61, g32p_row07_traceSegment_036_1336_0061, g32p_row07_traceSegment_036_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_036 1215 243 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1215 121 122, g32p_row07_traceSegment_036_1215_0121, g32p_row07_traceSegment_036_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_036 972 486 = [0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 972 243 243, g32p_row07_traceSegment_036_0972_0243, g32p_row07_traceSegment_036_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1458 15 15, g32p_row07_traceSegment_036_1458_0015, g32p_row07_traceSegment_036_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1488 15 15, g32p_row07_traceSegment_036_1488_0015, g32p_row07_traceSegment_036_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_036 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1458 30 30, g32p_row07_traceSegment_036_1458_0030, g32p_row07_traceSegment_036_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1518 15 15, g32p_row07_traceSegment_036_1518_0015, g32p_row07_traceSegment_036_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1548 15 16, g32p_row07_traceSegment_036_1548_0015, g32p_row07_traceSegment_036_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1518 30 31, g32p_row07_traceSegment_036_1518_0030, g32p_row07_traceSegment_036_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_036 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1458 60 61, g32p_row07_traceSegment_036_1458_0060, g32p_row07_traceSegment_036_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1579 15 15, g32p_row07_traceSegment_036_1579_0015, g32p_row07_traceSegment_036_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1609 15 16, g32p_row07_traceSegment_036_1609_0015, g32p_row07_traceSegment_036_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1579 30 31, g32p_row07_traceSegment_036_1579_0030, g32p_row07_traceSegment_036_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1640 15 15, g32p_row07_traceSegment_036_1640_0015, g32p_row07_traceSegment_036_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1670 15 16, g32p_row07_traceSegment_036_1670_0015, g32p_row07_traceSegment_036_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1640 30 31, g32p_row07_traceSegment_036_1640_0030, g32p_row07_traceSegment_036_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_036 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1579 61 61, g32p_row07_traceSegment_036_1579_0061, g32p_row07_traceSegment_036_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_036 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1458 121 122, g32p_row07_traceSegment_036_1458_0121, g32p_row07_traceSegment_036_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1701 15 15, g32p_row07_traceSegment_036_1701_0015, g32p_row07_traceSegment_036_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1731 15 15, g32p_row07_traceSegment_036_1731_0015, g32p_row07_traceSegment_036_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_036 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1701 30 30, g32p_row07_traceSegment_036_1701_0030, g32p_row07_traceSegment_036_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1761 15 15, g32p_row07_traceSegment_036_1761_0015, g32p_row07_traceSegment_036_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1791 15 16, g32p_row07_traceSegment_036_1791_0015, g32p_row07_traceSegment_036_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1761 30 31, g32p_row07_traceSegment_036_1761_0030, g32p_row07_traceSegment_036_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_036 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1701 60 61, g32p_row07_traceSegment_036_1701_0060, g32p_row07_traceSegment_036_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1822 15 15, g32p_row07_traceSegment_036_1822_0015, g32p_row07_traceSegment_036_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1852 15 16, g32p_row07_traceSegment_036_1852_0015, g32p_row07_traceSegment_036_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1822 30 31, g32p_row07_traceSegment_036_1822_0030, g32p_row07_traceSegment_036_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_036 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1883 15 15, g32p_row07_traceSegment_036_1883_0015, g32p_row07_traceSegment_036_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_036 1913 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_036 1928 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_036_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_036 1913 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1913 15 16, g32p_row07_traceSegment_036_1913_0015, g32p_row07_traceSegment_036_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_036 1883 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1883 30 31, g32p_row07_traceSegment_036_1883_0030, g32p_row07_traceSegment_036_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_036 1822 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1822 61 61, g32p_row07_traceSegment_036_1822_0061, g32p_row07_traceSegment_036_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_036 1701 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1701 121 122, g32p_row07_traceSegment_036_1701_0121, g32p_row07_traceSegment_036_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_036_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_036 1458 486 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 1458 243 243, g32p_row07_traceSegment_036_1458_0243, g32p_row07_traceSegment_036_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_036 972 972 = [0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 972 486 486, g32p_row07_traceSegment_036_0972_0486, g32p_row07_traceSegment_036_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_036_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_036 0 1944 = [0, 0, 72] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_036 0 972 972, g32p_row07_traceSegment_036_0000_0972, g32p_row07_traceSegment_036_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_036 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 36 = [0, 0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_036_0000_1944

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row07_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row07_supplierClassifier (Fin.ofNat 1944 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row07_characterValues (Fin.ofNat 1944 k))).val 1 else []

private theorem g32p_row07_traceSegment_037_0000_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 0 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0015_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 15 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0000_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 0 15 15, g32p_row07_traceSegment_037_0000_0015, g32p_row07_traceSegment_037_0015_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0030_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 30 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0045_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 45 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0030_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 30 15 15, g32p_row07_traceSegment_037_0030_0015, g32p_row07_traceSegment_037_0045_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0000_0060 : g32p_coeffSegment g32p_row07_traceSegment_037 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 0 30 30, g32p_row07_traceSegment_037_0000_0030, g32p_row07_traceSegment_037_0030_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0060_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 60 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0075_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 75 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0060_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 60 15 15, g32p_row07_traceSegment_037_0060_0015, g32p_row07_traceSegment_037_0075_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0090_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 90 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0105_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 105 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0090_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 90 15 16, g32p_row07_traceSegment_037_0090_0015, g32p_row07_traceSegment_037_0105_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0060_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 60 30 31, g32p_row07_traceSegment_037_0060_0030, g32p_row07_traceSegment_037_0090_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0000_0121 : g32p_coeffSegment g32p_row07_traceSegment_037 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 0 60 61, g32p_row07_traceSegment_037_0000_0060, g32p_row07_traceSegment_037_0060_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0121_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 121 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0136_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 136 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0121_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 121 15 15, g32p_row07_traceSegment_037_0121_0015, g32p_row07_traceSegment_037_0136_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0151_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 151 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0166_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 166 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0151_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 151 15 16, g32p_row07_traceSegment_037_0151_0015, g32p_row07_traceSegment_037_0166_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0121_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 121 30 31, g32p_row07_traceSegment_037_0121_0030, g32p_row07_traceSegment_037_0151_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0182_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 182 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0197_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 197 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0182_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 182 15 15, g32p_row07_traceSegment_037_0182_0015, g32p_row07_traceSegment_037_0197_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0212_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 212 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0227_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 227 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0212_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 212 15 16, g32p_row07_traceSegment_037_0212_0015, g32p_row07_traceSegment_037_0227_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0182_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 182 30 31, g32p_row07_traceSegment_037_0182_0030, g32p_row07_traceSegment_037_0212_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0121_0122 : g32p_coeffSegment g32p_row07_traceSegment_037 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 121 61 61, g32p_row07_traceSegment_037_0121_0061, g32p_row07_traceSegment_037_0182_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0000_0243 : g32p_coeffSegment g32p_row07_traceSegment_037 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 0 121 122, g32p_row07_traceSegment_037_0000_0121, g32p_row07_traceSegment_037_0121_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0243_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 243 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0258_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 258 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0243_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 243 15 15, g32p_row07_traceSegment_037_0243_0015, g32p_row07_traceSegment_037_0258_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0273_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 273 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0288_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 288 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0273_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 273 15 15, g32p_row07_traceSegment_037_0273_0015, g32p_row07_traceSegment_037_0288_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0243_0060 : g32p_coeffSegment g32p_row07_traceSegment_037 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 243 30 30, g32p_row07_traceSegment_037_0243_0030, g32p_row07_traceSegment_037_0273_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0303_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 303 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0318_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 318 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0303_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 303 15 15, g32p_row07_traceSegment_037_0303_0015, g32p_row07_traceSegment_037_0318_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0333_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 333 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0348_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 348 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0333_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 333 15 16, g32p_row07_traceSegment_037_0333_0015, g32p_row07_traceSegment_037_0348_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0303_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 303 30 31, g32p_row07_traceSegment_037_0303_0030, g32p_row07_traceSegment_037_0333_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0243_0121 : g32p_coeffSegment g32p_row07_traceSegment_037 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 243 60 61, g32p_row07_traceSegment_037_0243_0060, g32p_row07_traceSegment_037_0303_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0364_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 364 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0379_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 379 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0364_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 364 15 15, g32p_row07_traceSegment_037_0364_0015, g32p_row07_traceSegment_037_0379_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0394_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 394 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0409_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 409 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0394_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 394 15 16, g32p_row07_traceSegment_037_0394_0015, g32p_row07_traceSegment_037_0409_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0364_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 364 30 31, g32p_row07_traceSegment_037_0364_0030, g32p_row07_traceSegment_037_0394_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0425_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 425 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0440_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 440 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0425_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 425 15 15, g32p_row07_traceSegment_037_0425_0015, g32p_row07_traceSegment_037_0440_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0455_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 455 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0470_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 470 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0455_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 455 15 16, g32p_row07_traceSegment_037_0455_0015, g32p_row07_traceSegment_037_0470_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0425_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 425 30 31, g32p_row07_traceSegment_037_0425_0030, g32p_row07_traceSegment_037_0455_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0364_0122 : g32p_coeffSegment g32p_row07_traceSegment_037 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 364 61 61, g32p_row07_traceSegment_037_0364_0061, g32p_row07_traceSegment_037_0425_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0243_0243 : g32p_coeffSegment g32p_row07_traceSegment_037 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 243 121 122, g32p_row07_traceSegment_037_0243_0121, g32p_row07_traceSegment_037_0364_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0000_0486 : g32p_coeffSegment g32p_row07_traceSegment_037 0 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 0 243 243, g32p_row07_traceSegment_037_0000_0243, g32p_row07_traceSegment_037_0243_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0486_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 486 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0501_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 501 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0486_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 486 15 15, g32p_row07_traceSegment_037_0486_0015, g32p_row07_traceSegment_037_0501_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0516_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 516 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0531_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 531 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0516_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 516 15 15, g32p_row07_traceSegment_037_0516_0015, g32p_row07_traceSegment_037_0531_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0486_0060 : g32p_coeffSegment g32p_row07_traceSegment_037 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 486 30 30, g32p_row07_traceSegment_037_0486_0030, g32p_row07_traceSegment_037_0516_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0546_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 546 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0561_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 561 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0546_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 546 15 15, g32p_row07_traceSegment_037_0546_0015, g32p_row07_traceSegment_037_0561_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0576_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 576 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0591_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 591 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0576_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 576 15 16, g32p_row07_traceSegment_037_0576_0015, g32p_row07_traceSegment_037_0591_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0546_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 546 30 31, g32p_row07_traceSegment_037_0546_0030, g32p_row07_traceSegment_037_0576_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0486_0121 : g32p_coeffSegment g32p_row07_traceSegment_037 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 486 60 61, g32p_row07_traceSegment_037_0486_0060, g32p_row07_traceSegment_037_0546_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0607_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 607 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0622_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 622 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0607_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 607 15 15, g32p_row07_traceSegment_037_0607_0015, g32p_row07_traceSegment_037_0622_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0637_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 637 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0652_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 652 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0637_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 637 15 16, g32p_row07_traceSegment_037_0637_0015, g32p_row07_traceSegment_037_0652_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0607_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 607 30 31, g32p_row07_traceSegment_037_0607_0030, g32p_row07_traceSegment_037_0637_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0668_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 668 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0683_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 683 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0668_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 668 15 15, g32p_row07_traceSegment_037_0668_0015, g32p_row07_traceSegment_037_0683_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0698_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 698 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0713_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 713 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0698_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 698 15 16, g32p_row07_traceSegment_037_0698_0015, g32p_row07_traceSegment_037_0713_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0668_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 668 30 31, g32p_row07_traceSegment_037_0668_0030, g32p_row07_traceSegment_037_0698_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0607_0122 : g32p_coeffSegment g32p_row07_traceSegment_037 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 607 61 61, g32p_row07_traceSegment_037_0607_0061, g32p_row07_traceSegment_037_0668_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0486_0243 : g32p_coeffSegment g32p_row07_traceSegment_037 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 486 121 122, g32p_row07_traceSegment_037_0486_0121, g32p_row07_traceSegment_037_0607_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0729_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 729 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0744_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 744 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0729_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 729 15 15, g32p_row07_traceSegment_037_0729_0015, g32p_row07_traceSegment_037_0744_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0759_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 759 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0774_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 774 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0759_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 759 15 15, g32p_row07_traceSegment_037_0759_0015, g32p_row07_traceSegment_037_0774_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0729_0060 : g32p_coeffSegment g32p_row07_traceSegment_037 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 729 30 30, g32p_row07_traceSegment_037_0729_0030, g32p_row07_traceSegment_037_0759_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0789_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 789 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0804_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 804 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0789_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 789 15 15, g32p_row07_traceSegment_037_0789_0015, g32p_row07_traceSegment_037_0804_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0819_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 819 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0834_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 834 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0819_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 819 15 16, g32p_row07_traceSegment_037_0819_0015, g32p_row07_traceSegment_037_0834_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0789_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 789 30 31, g32p_row07_traceSegment_037_0789_0030, g32p_row07_traceSegment_037_0819_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0729_0121 : g32p_coeffSegment g32p_row07_traceSegment_037 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 729 60 61, g32p_row07_traceSegment_037_0729_0060, g32p_row07_traceSegment_037_0789_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0850_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 850 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0865_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 865 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0850_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 850 15 15, g32p_row07_traceSegment_037_0850_0015, g32p_row07_traceSegment_037_0865_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0880_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 880 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0895_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 895 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0880_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 880 15 16, g32p_row07_traceSegment_037_0880_0015, g32p_row07_traceSegment_037_0895_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0850_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 850 30 31, g32p_row07_traceSegment_037_0850_0030, g32p_row07_traceSegment_037_0880_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0911_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 911 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0926_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 926 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0911_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 911 15 15, g32p_row07_traceSegment_037_0911_0015, g32p_row07_traceSegment_037_0926_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0941_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 941 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0956_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 956 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0941_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 941 15 16, g32p_row07_traceSegment_037_0941_0015, g32p_row07_traceSegment_037_0956_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0911_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 911 30 31, g32p_row07_traceSegment_037_0911_0030, g32p_row07_traceSegment_037_0941_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0850_0122 : g32p_coeffSegment g32p_row07_traceSegment_037 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 850 61 61, g32p_row07_traceSegment_037_0850_0061, g32p_row07_traceSegment_037_0911_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0729_0243 : g32p_coeffSegment g32p_row07_traceSegment_037 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 729 121 122, g32p_row07_traceSegment_037_0729_0121, g32p_row07_traceSegment_037_0850_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0486_0486 : g32p_coeffSegment g32p_row07_traceSegment_037 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 486 243 243, g32p_row07_traceSegment_037_0486_0243, g32p_row07_traceSegment_037_0729_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0000_0972 : g32p_coeffSegment g32p_row07_traceSegment_037 0 972 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 0 486 486, g32p_row07_traceSegment_037_0000_0486, g32p_row07_traceSegment_037_0486_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0972_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 972 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0987_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 987 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_0972_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 972 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 972 15 15, g32p_row07_traceSegment_037_0972_0015, g32p_row07_traceSegment_037_0987_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1002_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1002 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1017_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1017 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1002_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1002 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1002 15 15, g32p_row07_traceSegment_037_1002_0015, g32p_row07_traceSegment_037_1017_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0972_0060 : g32p_coeffSegment g32p_row07_traceSegment_037 972 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 972 30 30, g32p_row07_traceSegment_037_0972_0030, g32p_row07_traceSegment_037_1002_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1032_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1032 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1047_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1047 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1032_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1032 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1032 15 15, g32p_row07_traceSegment_037_1032_0015, g32p_row07_traceSegment_037_1047_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1062_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1062 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1077_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1077 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1062_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1062 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1062 15 16, g32p_row07_traceSegment_037_1062_0015, g32p_row07_traceSegment_037_1077_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1032_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1032 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1032 30 31, g32p_row07_traceSegment_037_1032_0030, g32p_row07_traceSegment_037_1062_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0972_0121 : g32p_coeffSegment g32p_row07_traceSegment_037 972 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 972 60 61, g32p_row07_traceSegment_037_0972_0060, g32p_row07_traceSegment_037_1032_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1093_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1093 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1108_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1108 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1093_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1093 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1093 15 15, g32p_row07_traceSegment_037_1093_0015, g32p_row07_traceSegment_037_1108_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1123_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1123 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1138_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1138 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1123_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1123 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1123 15 16, g32p_row07_traceSegment_037_1123_0015, g32p_row07_traceSegment_037_1138_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1093_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1093 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1093 30 31, g32p_row07_traceSegment_037_1093_0030, g32p_row07_traceSegment_037_1123_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1154_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1154 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1169_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1169 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1154_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1154 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1154 15 15, g32p_row07_traceSegment_037_1154_0015, g32p_row07_traceSegment_037_1169_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1184_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1184 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1199_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1199 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1184_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1184 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1184 15 16, g32p_row07_traceSegment_037_1184_0015, g32p_row07_traceSegment_037_1199_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1154_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1154 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1154 30 31, g32p_row07_traceSegment_037_1154_0030, g32p_row07_traceSegment_037_1184_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1093_0122 : g32p_coeffSegment g32p_row07_traceSegment_037 1093 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1093 61 61, g32p_row07_traceSegment_037_1093_0061, g32p_row07_traceSegment_037_1154_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0972_0243 : g32p_coeffSegment g32p_row07_traceSegment_037 972 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 972 121 122, g32p_row07_traceSegment_037_0972_0121, g32p_row07_traceSegment_037_1093_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1215_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1215 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1230_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1230 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1215_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1215 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1215 15 15, g32p_row07_traceSegment_037_1215_0015, g32p_row07_traceSegment_037_1230_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1245_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1245 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1260_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1260 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1245_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1245 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1245 15 15, g32p_row07_traceSegment_037_1245_0015, g32p_row07_traceSegment_037_1260_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1215_0060 : g32p_coeffSegment g32p_row07_traceSegment_037 1215 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1215 30 30, g32p_row07_traceSegment_037_1215_0030, g32p_row07_traceSegment_037_1245_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1275_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1275 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1290_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1290 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1275_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1275 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1275 15 15, g32p_row07_traceSegment_037_1275_0015, g32p_row07_traceSegment_037_1290_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1305_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1305 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1320_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1320 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1305_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1305 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1305 15 16, g32p_row07_traceSegment_037_1305_0015, g32p_row07_traceSegment_037_1320_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1275_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1275 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1275 30 31, g32p_row07_traceSegment_037_1275_0030, g32p_row07_traceSegment_037_1305_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1215_0121 : g32p_coeffSegment g32p_row07_traceSegment_037 1215 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1215 60 61, g32p_row07_traceSegment_037_1215_0060, g32p_row07_traceSegment_037_1275_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1336_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1336 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1351_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1351 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1336_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1336 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1336 15 15, g32p_row07_traceSegment_037_1336_0015, g32p_row07_traceSegment_037_1351_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1366_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1366 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1381_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1381 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1366_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1366 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1366 15 16, g32p_row07_traceSegment_037_1366_0015, g32p_row07_traceSegment_037_1381_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1336_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1336 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1336 30 31, g32p_row07_traceSegment_037_1336_0030, g32p_row07_traceSegment_037_1366_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1397_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1397 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1412_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1412 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1397_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1397 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1397 15 15, g32p_row07_traceSegment_037_1397_0015, g32p_row07_traceSegment_037_1412_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1427_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1427 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1442_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1442 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1427_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1427 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1427 15 16, g32p_row07_traceSegment_037_1427_0015, g32p_row07_traceSegment_037_1442_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1397_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1397 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1397 30 31, g32p_row07_traceSegment_037_1397_0030, g32p_row07_traceSegment_037_1427_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1336_0122 : g32p_coeffSegment g32p_row07_traceSegment_037 1336 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1336 61 61, g32p_row07_traceSegment_037_1336_0061, g32p_row07_traceSegment_037_1397_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1215_0243 : g32p_coeffSegment g32p_row07_traceSegment_037 1215 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1215 121 122, g32p_row07_traceSegment_037_1215_0121, g32p_row07_traceSegment_037_1336_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0972_0486 : g32p_coeffSegment g32p_row07_traceSegment_037 972 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 972 243 243, g32p_row07_traceSegment_037_0972_0243, g32p_row07_traceSegment_037_1215_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1458_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1458 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1473_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1473 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1458_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1458 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1458 15 15, g32p_row07_traceSegment_037_1458_0015, g32p_row07_traceSegment_037_1473_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1488_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1488 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1503_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1503 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1488_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1488 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1488 15 15, g32p_row07_traceSegment_037_1488_0015, g32p_row07_traceSegment_037_1503_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1458_0060 : g32p_coeffSegment g32p_row07_traceSegment_037 1458 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1458 30 30, g32p_row07_traceSegment_037_1458_0030, g32p_row07_traceSegment_037_1488_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1518_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1518 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1533_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1533 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1518_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1518 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1518 15 15, g32p_row07_traceSegment_037_1518_0015, g32p_row07_traceSegment_037_1533_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1548_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1548 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1563_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1563 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1548_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1548 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1548 15 16, g32p_row07_traceSegment_037_1548_0015, g32p_row07_traceSegment_037_1563_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1518_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1518 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1518 30 31, g32p_row07_traceSegment_037_1518_0030, g32p_row07_traceSegment_037_1548_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1458_0121 : g32p_coeffSegment g32p_row07_traceSegment_037 1458 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1458 60 61, g32p_row07_traceSegment_037_1458_0060, g32p_row07_traceSegment_037_1518_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1579_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1579 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1594_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1594 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1579_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1579 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1579 15 15, g32p_row07_traceSegment_037_1579_0015, g32p_row07_traceSegment_037_1594_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1609_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1609 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1624_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1624 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1609_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1609 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1609 15 16, g32p_row07_traceSegment_037_1609_0015, g32p_row07_traceSegment_037_1624_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1579_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1579 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1579 30 31, g32p_row07_traceSegment_037_1579_0030, g32p_row07_traceSegment_037_1609_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1640_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1640 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1655_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1655 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1640_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1640 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1640 15 15, g32p_row07_traceSegment_037_1640_0015, g32p_row07_traceSegment_037_1655_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1670_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1670 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1685_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1685 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1670_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1670 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1670 15 16, g32p_row07_traceSegment_037_1670_0015, g32p_row07_traceSegment_037_1685_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1640_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1640 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1640 30 31, g32p_row07_traceSegment_037_1640_0030, g32p_row07_traceSegment_037_1670_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1579_0122 : g32p_coeffSegment g32p_row07_traceSegment_037 1579 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1579 61 61, g32p_row07_traceSegment_037_1579_0061, g32p_row07_traceSegment_037_1640_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1458_0243 : g32p_coeffSegment g32p_row07_traceSegment_037 1458 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1458 121 122, g32p_row07_traceSegment_037_1458_0121, g32p_row07_traceSegment_037_1579_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1701_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1701 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1716_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1716 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1701_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1701 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1701 15 15, g32p_row07_traceSegment_037_1701_0015, g32p_row07_traceSegment_037_1716_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1731_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1731 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1746_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1746 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1731_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1731 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1731 15 15, g32p_row07_traceSegment_037_1731_0015, g32p_row07_traceSegment_037_1746_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1701_0060 : g32p_coeffSegment g32p_row07_traceSegment_037 1701 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1701 30 30, g32p_row07_traceSegment_037_1701_0030, g32p_row07_traceSegment_037_1731_0030]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1761_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1761 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1776_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1776 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1761_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1761 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1761 15 15, g32p_row07_traceSegment_037_1761_0015, g32p_row07_traceSegment_037_1776_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1791_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1791 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1806_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1806 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1791_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1791 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1791 15 16, g32p_row07_traceSegment_037_1791_0015, g32p_row07_traceSegment_037_1806_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1761_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1761 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1761 30 31, g32p_row07_traceSegment_037_1761_0030, g32p_row07_traceSegment_037_1791_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1701_0121 : g32p_coeffSegment g32p_row07_traceSegment_037 1701 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1701 60 61, g32p_row07_traceSegment_037_1701_0060, g32p_row07_traceSegment_037_1761_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1822_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1822 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1837_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1837 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1822_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1822 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1822 15 15, g32p_row07_traceSegment_037_1822_0015, g32p_row07_traceSegment_037_1837_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1852_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1852 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1867_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1867 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1852_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1852 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1852 15 16, g32p_row07_traceSegment_037_1852_0015, g32p_row07_traceSegment_037_1867_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1822_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1822 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1822 30 31, g32p_row07_traceSegment_037_1822_0030, g32p_row07_traceSegment_037_1852_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1883_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1883 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1898_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1898 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1883_0030 : g32p_coeffSegment g32p_row07_traceSegment_037 1883 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1883 15 15, g32p_row07_traceSegment_037_1883_0015, g32p_row07_traceSegment_037_1898_0015]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1913_0015 : g32p_coeffSegment g32p_row07_traceSegment_037 1913 15 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1928_0016 : g32p_coeffSegment g32p_row07_traceSegment_037 1928 16 = [] := by
  decide +kernel

private theorem g32p_row07_traceSegment_037_1913_0031 : g32p_coeffSegment g32p_row07_traceSegment_037 1913 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1913 15 16, g32p_row07_traceSegment_037_1913_0015, g32p_row07_traceSegment_037_1928_0016]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1883_0061 : g32p_coeffSegment g32p_row07_traceSegment_037 1883 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1883 30 31, g32p_row07_traceSegment_037_1883_0030, g32p_row07_traceSegment_037_1913_0031]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1822_0122 : g32p_coeffSegment g32p_row07_traceSegment_037 1822 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1822 61 61, g32p_row07_traceSegment_037_1822_0061, g32p_row07_traceSegment_037_1883_0061]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1701_0243 : g32p_coeffSegment g32p_row07_traceSegment_037 1701 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1701 121 122, g32p_row07_traceSegment_037_1701_0121, g32p_row07_traceSegment_037_1822_0122]
  decide +kernel

private theorem g32p_row07_traceSegment_037_1458_0486 : g32p_coeffSegment g32p_row07_traceSegment_037 1458 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 1458 243 243, g32p_row07_traceSegment_037_1458_0243, g32p_row07_traceSegment_037_1701_0243]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0972_0972 : g32p_coeffSegment g32p_row07_traceSegment_037 972 972 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 972 486 486, g32p_row07_traceSegment_037_0972_0486, g32p_row07_traceSegment_037_1458_0486]
  decide +kernel

private theorem g32p_row07_traceSegment_037_0000_1944 : g32p_coeffSegment g32p_row07_traceSegment_037 0 1944 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row07_traceSegment_037 0 972 972, g32p_row07_traceSegment_037_0000_0972, g32p_row07_traceSegment_037_0972_0972]
  decide +kernel

theorem g32p_row07_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row07_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row07_characterValues j)).val) 37 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row07_traceSegment_037_0000_1944

end HodgeLean.Foundations.Program

end
end
