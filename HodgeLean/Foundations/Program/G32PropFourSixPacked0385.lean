import HodgeLean.Foundations.Program.G32PropFourSixPacked0382
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0384

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_053 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 53 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_053_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 0 15 15, g32p_row21_traceSegment_053_0000_0015, g32p_row21_traceSegment_053_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 30 15 15, g32p_row21_traceSegment_053_0030_0015, g32p_row21_traceSegment_053_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_053 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 0 30 30, g32p_row21_traceSegment_053_0000_0030, g32p_row21_traceSegment_053_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 60 15 15, g32p_row21_traceSegment_053_0060_0015, g32p_row21_traceSegment_053_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 90 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 105 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 90 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 90 15 16, g32p_row21_traceSegment_053_0090_0015, g32p_row21_traceSegment_053_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 60 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 60 30 31, g32p_row21_traceSegment_053_0060_0030, g32p_row21_traceSegment_053_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_053 0 121 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 0 60 61, g32p_row21_traceSegment_053_0000_0060, g32p_row21_traceSegment_053_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 136 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 121 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 121 15 15, g32p_row21_traceSegment_053_0121_0015, g32p_row21_traceSegment_053_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 151 15 16, g32p_row21_traceSegment_053_0151_0015, g32p_row21_traceSegment_053_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 121 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 121 30 31, g32p_row21_traceSegment_053_0121_0030, g32p_row21_traceSegment_053_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 182 15 15, g32p_row21_traceSegment_053_0182_0015, g32p_row21_traceSegment_053_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 212 15 16, g32p_row21_traceSegment_053_0212_0015, g32p_row21_traceSegment_053_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 182 30 31, g32p_row21_traceSegment_053_0182_0030, g32p_row21_traceSegment_053_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_053 121 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 121 61 61, g32p_row21_traceSegment_053_0121_0061, g32p_row21_traceSegment_053_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_053 0 243 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 0 121 122, g32p_row21_traceSegment_053_0000_0121, g32p_row21_traceSegment_053_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 243 15 15, g32p_row21_traceSegment_053_0243_0015, g32p_row21_traceSegment_053_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 273 15 15, g32p_row21_traceSegment_053_0273_0015, g32p_row21_traceSegment_053_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_053 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 243 30 30, g32p_row21_traceSegment_053_0243_0030, g32p_row21_traceSegment_053_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 303 15 15, g32p_row21_traceSegment_053_0303_0015, g32p_row21_traceSegment_053_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 333 15 16, g32p_row21_traceSegment_053_0333_0015, g32p_row21_traceSegment_053_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 303 30 31, g32p_row21_traceSegment_053_0303_0030, g32p_row21_traceSegment_053_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_053 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 243 60 61, g32p_row21_traceSegment_053_0243_0060, g32p_row21_traceSegment_053_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 364 15 15, g32p_row21_traceSegment_053_0364_0015, g32p_row21_traceSegment_053_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 394 15 16, g32p_row21_traceSegment_053_0394_0015, g32p_row21_traceSegment_053_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 364 30 31, g32p_row21_traceSegment_053_0364_0030, g32p_row21_traceSegment_053_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 425 15 15, g32p_row21_traceSegment_053_0425_0015, g32p_row21_traceSegment_053_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 455 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 455 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 455 15 16, g32p_row21_traceSegment_053_0455_0015, g32p_row21_traceSegment_053_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 425 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 425 30 31, g32p_row21_traceSegment_053_0425_0030, g32p_row21_traceSegment_053_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_053 364 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 364 61 61, g32p_row21_traceSegment_053_0364_0061, g32p_row21_traceSegment_053_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_053 243 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 243 121 122, g32p_row21_traceSegment_053_0243_0121, g32p_row21_traceSegment_053_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_053 0 486 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 0 243 243, g32p_row21_traceSegment_053_0000_0243, g32p_row21_traceSegment_053_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 501 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 486 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 486 15 15, g32p_row21_traceSegment_053_0486_0015, g32p_row21_traceSegment_053_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 516 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 531 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 516 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 516 15 15, g32p_row21_traceSegment_053_0516_0015, g32p_row21_traceSegment_053_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_053 486 60 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 486 30 30, g32p_row21_traceSegment_053_0486_0030, g32p_row21_traceSegment_053_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 546 15 15, g32p_row21_traceSegment_053_0546_0015, g32p_row21_traceSegment_053_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 576 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 576 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 576 15 16, g32p_row21_traceSegment_053_0576_0015, g32p_row21_traceSegment_053_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 546 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 546 30 31, g32p_row21_traceSegment_053_0546_0030, g32p_row21_traceSegment_053_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_053 486 121 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 486 60 61, g32p_row21_traceSegment_053_0486_0060, g32p_row21_traceSegment_053_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 607 15 15, g32p_row21_traceSegment_053_0607_0015, g32p_row21_traceSegment_053_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 637 15 16, g32p_row21_traceSegment_053_0637_0015, g32p_row21_traceSegment_053_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 607 30 31, g32p_row21_traceSegment_053_0607_0030, g32p_row21_traceSegment_053_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 668 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 683 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 668 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 668 15 15, g32p_row21_traceSegment_053_0668_0015, g32p_row21_traceSegment_053_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 698 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 713 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 698 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 698 15 16, g32p_row21_traceSegment_053_0698_0015, g32p_row21_traceSegment_053_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 668 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 668 30 31, g32p_row21_traceSegment_053_0668_0030, g32p_row21_traceSegment_053_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_053 607 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 607 61 61, g32p_row21_traceSegment_053_0607_0061, g32p_row21_traceSegment_053_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_053 486 243 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 486 121 122, g32p_row21_traceSegment_053_0486_0121, g32p_row21_traceSegment_053_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 729 15 15, g32p_row21_traceSegment_053_0729_0015, g32p_row21_traceSegment_053_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 774 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 759 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 759 15 15, g32p_row21_traceSegment_053_0759_0015, g32p_row21_traceSegment_053_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_053 729 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 729 30 30, g32p_row21_traceSegment_053_0729_0030, g32p_row21_traceSegment_053_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 789 15 15, g32p_row21_traceSegment_053_0789_0015, g32p_row21_traceSegment_053_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 819 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 819 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 819 15 16, g32p_row21_traceSegment_053_0819_0015, g32p_row21_traceSegment_053_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 789 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 789 30 31, g32p_row21_traceSegment_053_0789_0030, g32p_row21_traceSegment_053_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_053 729 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 729 60 61, g32p_row21_traceSegment_053_0729_0060, g32p_row21_traceSegment_053_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 865 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 850 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 850 15 15, g32p_row21_traceSegment_053_0850_0015, g32p_row21_traceSegment_053_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 880 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 880 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 880 15 16, g32p_row21_traceSegment_053_0880_0015, g32p_row21_traceSegment_053_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 850 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 850 30 31, g32p_row21_traceSegment_053_0850_0030, g32p_row21_traceSegment_053_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_053 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 911 15 15, g32p_row21_traceSegment_053_0911_0015, g32p_row21_traceSegment_053_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_053 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_053 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_053_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_053 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 941 15 16, g32p_row21_traceSegment_053_0941_0015, g32p_row21_traceSegment_053_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_053 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 911 30 31, g32p_row21_traceSegment_053_0911_0030, g32p_row21_traceSegment_053_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_053 850 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 850 61 61, g32p_row21_traceSegment_053_0850_0061, g32p_row21_traceSegment_053_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_053 729 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 729 121 122, g32p_row21_traceSegment_053_0729_0121, g32p_row21_traceSegment_053_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_053 486 486 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 486 243 243, g32p_row21_traceSegment_053_0486_0243, g32p_row21_traceSegment_053_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_053_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_053 0 972 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_053 0 486 486, g32p_row21_traceSegment_053_0000_0486, g32p_row21_traceSegment_053_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_053 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 53 = [0, 0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_053_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_054 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 54 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_054_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 0 15 15, g32p_row21_traceSegment_054_0000_0015, g32p_row21_traceSegment_054_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 30 15 15, g32p_row21_traceSegment_054_0030_0015, g32p_row21_traceSegment_054_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_054 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 0 30 30, g32p_row21_traceSegment_054_0000_0030, g32p_row21_traceSegment_054_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 60 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 75 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 60 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 60 15 15, g32p_row21_traceSegment_054_0060_0015, g32p_row21_traceSegment_054_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 90 15 16, g32p_row21_traceSegment_054_0090_0015, g32p_row21_traceSegment_054_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 60 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 60 30 31, g32p_row21_traceSegment_054_0060_0030, g32p_row21_traceSegment_054_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_054 0 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 0 60 61, g32p_row21_traceSegment_054_0000_0060, g32p_row21_traceSegment_054_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 121 15 15, g32p_row21_traceSegment_054_0121_0015, g32p_row21_traceSegment_054_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 151 15 16, g32p_row21_traceSegment_054_0151_0015, g32p_row21_traceSegment_054_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 121 30 31, g32p_row21_traceSegment_054_0121_0030, g32p_row21_traceSegment_054_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 182 15 15, g32p_row21_traceSegment_054_0182_0015, g32p_row21_traceSegment_054_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 212 15 16, g32p_row21_traceSegment_054_0212_0015, g32p_row21_traceSegment_054_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 182 30 31, g32p_row21_traceSegment_054_0182_0030, g32p_row21_traceSegment_054_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_054 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 121 61 61, g32p_row21_traceSegment_054_0121_0061, g32p_row21_traceSegment_054_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_054 0 243 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 0 121 122, g32p_row21_traceSegment_054_0000_0121, g32p_row21_traceSegment_054_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 243 15 15, g32p_row21_traceSegment_054_0243_0015, g32p_row21_traceSegment_054_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 273 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 288 15 = [3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 273 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 273 15 15, g32p_row21_traceSegment_054_0273_0015, g32p_row21_traceSegment_054_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_054 243 60 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 243 30 30, g32p_row21_traceSegment_054_0243_0030, g32p_row21_traceSegment_054_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 303 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 303 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 303 15 15, g32p_row21_traceSegment_054_0303_0015, g32p_row21_traceSegment_054_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 333 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 333 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 333 15 16, g32p_row21_traceSegment_054_0333_0015, g32p_row21_traceSegment_054_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 303 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 303 30 31, g32p_row21_traceSegment_054_0303_0030, g32p_row21_traceSegment_054_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_054 243 121 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 243 60 61, g32p_row21_traceSegment_054_0243_0060, g32p_row21_traceSegment_054_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 364 15 15, g32p_row21_traceSegment_054_0364_0015, g32p_row21_traceSegment_054_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 394 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 394 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 394 15 16, g32p_row21_traceSegment_054_0394_0015, g32p_row21_traceSegment_054_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 364 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 364 30 31, g32p_row21_traceSegment_054_0364_0030, g32p_row21_traceSegment_054_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 425 15 15, g32p_row21_traceSegment_054_0425_0015, g32p_row21_traceSegment_054_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 455 15 16, g32p_row21_traceSegment_054_0455_0015, g32p_row21_traceSegment_054_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 425 30 31, g32p_row21_traceSegment_054_0425_0030, g32p_row21_traceSegment_054_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_054 364 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 364 61 61, g32p_row21_traceSegment_054_0364_0061, g32p_row21_traceSegment_054_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_054 243 243 = [8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 243 121 122, g32p_row21_traceSegment_054_0243_0121, g32p_row21_traceSegment_054_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_054 0 486 = [11] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 0 243 243, g32p_row21_traceSegment_054_0000_0243, g32p_row21_traceSegment_054_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 486 15 15, g32p_row21_traceSegment_054_0486_0015, g32p_row21_traceSegment_054_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 516 15 15, g32p_row21_traceSegment_054_0516_0015, g32p_row21_traceSegment_054_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_054 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 486 30 30, g32p_row21_traceSegment_054_0486_0030, g32p_row21_traceSegment_054_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 546 15 15, g32p_row21_traceSegment_054_0546_0015, g32p_row21_traceSegment_054_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 576 15 16, g32p_row21_traceSegment_054_0576_0015, g32p_row21_traceSegment_054_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 546 30 31, g32p_row21_traceSegment_054_0546_0030, g32p_row21_traceSegment_054_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_054 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 486 60 61, g32p_row21_traceSegment_054_0486_0060, g32p_row21_traceSegment_054_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 607 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 607 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 607 15 15, g32p_row21_traceSegment_054_0607_0015, g32p_row21_traceSegment_054_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 637 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 652 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 637 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 637 15 16, g32p_row21_traceSegment_054_0637_0015, g32p_row21_traceSegment_054_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 607 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 607 30 31, g32p_row21_traceSegment_054_0607_0030, g32p_row21_traceSegment_054_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 683 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 668 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 668 15 15, g32p_row21_traceSegment_054_0668_0015, g32p_row21_traceSegment_054_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 698 15 16, g32p_row21_traceSegment_054_0698_0015, g32p_row21_traceSegment_054_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 668 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 668 30 31, g32p_row21_traceSegment_054_0668_0030, g32p_row21_traceSegment_054_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_054 607 122 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 607 61 61, g32p_row21_traceSegment_054_0607_0061, g32p_row21_traceSegment_054_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_054 486 243 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 486 121 122, g32p_row21_traceSegment_054_0486_0121, g32p_row21_traceSegment_054_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 729 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 744 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 729 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 729 15 15, g32p_row21_traceSegment_054_0729_0015, g32p_row21_traceSegment_054_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 759 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 759 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 759 15 15, g32p_row21_traceSegment_054_0759_0015, g32p_row21_traceSegment_054_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_054 729 60 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 729 30 30, g32p_row21_traceSegment_054_0729_0030, g32p_row21_traceSegment_054_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 789 15 15, g32p_row21_traceSegment_054_0789_0015, g32p_row21_traceSegment_054_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 819 15 16, g32p_row21_traceSegment_054_0819_0015, g32p_row21_traceSegment_054_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 789 30 31, g32p_row21_traceSegment_054_0789_0030, g32p_row21_traceSegment_054_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_054 729 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 729 60 61, g32p_row21_traceSegment_054_0729_0060, g32p_row21_traceSegment_054_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 850 15 15, g32p_row21_traceSegment_054_0850_0015, g32p_row21_traceSegment_054_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 880 15 16, g32p_row21_traceSegment_054_0880_0015, g32p_row21_traceSegment_054_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 850 30 31, g32p_row21_traceSegment_054_0850_0030, g32p_row21_traceSegment_054_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_054 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 911 15 15, g32p_row21_traceSegment_054_0911_0015, g32p_row21_traceSegment_054_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_054 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_054 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_054_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_054 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 941 15 16, g32p_row21_traceSegment_054_0941_0015, g32p_row21_traceSegment_054_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_054 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 911 30 31, g32p_row21_traceSegment_054_0911_0030, g32p_row21_traceSegment_054_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_054 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 850 61 61, g32p_row21_traceSegment_054_0850_0061, g32p_row21_traceSegment_054_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_054 729 243 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 729 121 122, g32p_row21_traceSegment_054_0729_0121, g32p_row21_traceSegment_054_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_054 486 486 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 486 243 243, g32p_row21_traceSegment_054_0486_0243, g32p_row21_traceSegment_054_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_054_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_054 0 972 = [18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_054 0 486 486, g32p_row21_traceSegment_054_0000_0486, g32p_row21_traceSegment_054_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_054 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 54 = [18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_054_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_056 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 56 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_056_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 0 15 15, g32p_row21_traceSegment_056_0000_0015, g32p_row21_traceSegment_056_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 30 15 15, g32p_row21_traceSegment_056_0030_0015, g32p_row21_traceSegment_056_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_056 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 0 30 30, g32p_row21_traceSegment_056_0000_0030, g32p_row21_traceSegment_056_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 60 15 15, g32p_row21_traceSegment_056_0060_0015, g32p_row21_traceSegment_056_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 90 15 16, g32p_row21_traceSegment_056_0090_0015, g32p_row21_traceSegment_056_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 60 30 31, g32p_row21_traceSegment_056_0060_0030, g32p_row21_traceSegment_056_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_056 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 0 60 61, g32p_row21_traceSegment_056_0000_0060, g32p_row21_traceSegment_056_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 121 15 15, g32p_row21_traceSegment_056_0121_0015, g32p_row21_traceSegment_056_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 151 15 16, g32p_row21_traceSegment_056_0151_0015, g32p_row21_traceSegment_056_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 121 30 31, g32p_row21_traceSegment_056_0121_0030, g32p_row21_traceSegment_056_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 182 15 15, g32p_row21_traceSegment_056_0182_0015, g32p_row21_traceSegment_056_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 212 15 16, g32p_row21_traceSegment_056_0212_0015, g32p_row21_traceSegment_056_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 182 30 31, g32p_row21_traceSegment_056_0182_0030, g32p_row21_traceSegment_056_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_056 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 121 61 61, g32p_row21_traceSegment_056_0121_0061, g32p_row21_traceSegment_056_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_056 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 0 121 122, g32p_row21_traceSegment_056_0000_0121, g32p_row21_traceSegment_056_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 243 15 15, g32p_row21_traceSegment_056_0243_0015, g32p_row21_traceSegment_056_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 273 15 15, g32p_row21_traceSegment_056_0273_0015, g32p_row21_traceSegment_056_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_056 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 243 30 30, g32p_row21_traceSegment_056_0243_0030, g32p_row21_traceSegment_056_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 303 15 15, g32p_row21_traceSegment_056_0303_0015, g32p_row21_traceSegment_056_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 333 15 16, g32p_row21_traceSegment_056_0333_0015, g32p_row21_traceSegment_056_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 303 30 31, g32p_row21_traceSegment_056_0303_0030, g32p_row21_traceSegment_056_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_056 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 243 60 61, g32p_row21_traceSegment_056_0243_0060, g32p_row21_traceSegment_056_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 364 15 15, g32p_row21_traceSegment_056_0364_0015, g32p_row21_traceSegment_056_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 394 15 16, g32p_row21_traceSegment_056_0394_0015, g32p_row21_traceSegment_056_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 364 30 31, g32p_row21_traceSegment_056_0364_0030, g32p_row21_traceSegment_056_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 425 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 440 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 425 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 425 15 15, g32p_row21_traceSegment_056_0425_0015, g32p_row21_traceSegment_056_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 455 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 470 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 455 31 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 455 15 16, g32p_row21_traceSegment_056_0455_0015, g32p_row21_traceSegment_056_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 425 61 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 425 30 31, g32p_row21_traceSegment_056_0425_0030, g32p_row21_traceSegment_056_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_056 364 122 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 364 61 61, g32p_row21_traceSegment_056_0364_0061, g32p_row21_traceSegment_056_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_056 243 243 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 243 121 122, g32p_row21_traceSegment_056_0243_0121, g32p_row21_traceSegment_056_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_056 0 486 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 0 243 243, g32p_row21_traceSegment_056_0000_0243, g32p_row21_traceSegment_056_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 486 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 486 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 486 15 15, g32p_row21_traceSegment_056_0486_0015, g32p_row21_traceSegment_056_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 516 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 516 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 516 15 15, g32p_row21_traceSegment_056_0516_0015, g32p_row21_traceSegment_056_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_056 486 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 486 30 30, g32p_row21_traceSegment_056_0486_0030, g32p_row21_traceSegment_056_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 546 15 15, g32p_row21_traceSegment_056_0546_0015, g32p_row21_traceSegment_056_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 576 15 16, g32p_row21_traceSegment_056_0576_0015, g32p_row21_traceSegment_056_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 546 30 31, g32p_row21_traceSegment_056_0546_0030, g32p_row21_traceSegment_056_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_056 486 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 486 60 61, g32p_row21_traceSegment_056_0486_0060, g32p_row21_traceSegment_056_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 607 15 15, g32p_row21_traceSegment_056_0607_0015, g32p_row21_traceSegment_056_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 637 15 16, g32p_row21_traceSegment_056_0637_0015, g32p_row21_traceSegment_056_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 607 30 31, g32p_row21_traceSegment_056_0607_0030, g32p_row21_traceSegment_056_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 668 15 15, g32p_row21_traceSegment_056_0668_0015, g32p_row21_traceSegment_056_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 698 15 16, g32p_row21_traceSegment_056_0698_0015, g32p_row21_traceSegment_056_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 668 30 31, g32p_row21_traceSegment_056_0668_0030, g32p_row21_traceSegment_056_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_056 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 607 61 61, g32p_row21_traceSegment_056_0607_0061, g32p_row21_traceSegment_056_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_056 486 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 486 121 122, g32p_row21_traceSegment_056_0486_0121, g32p_row21_traceSegment_056_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 729 15 15, g32p_row21_traceSegment_056_0729_0015, g32p_row21_traceSegment_056_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 759 15 15, g32p_row21_traceSegment_056_0759_0015, g32p_row21_traceSegment_056_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_056 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 729 30 30, g32p_row21_traceSegment_056_0729_0030, g32p_row21_traceSegment_056_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 789 15 15, g32p_row21_traceSegment_056_0789_0015, g32p_row21_traceSegment_056_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 819 15 16, g32p_row21_traceSegment_056_0819_0015, g32p_row21_traceSegment_056_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 789 30 31, g32p_row21_traceSegment_056_0789_0030, g32p_row21_traceSegment_056_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_056 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 729 60 61, g32p_row21_traceSegment_056_0729_0060, g32p_row21_traceSegment_056_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 850 15 15, g32p_row21_traceSegment_056_0850_0015, g32p_row21_traceSegment_056_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 880 15 16, g32p_row21_traceSegment_056_0880_0015, g32p_row21_traceSegment_056_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 850 30 31, g32p_row21_traceSegment_056_0850_0030, g32p_row21_traceSegment_056_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_056 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 911 15 15, g32p_row21_traceSegment_056_0911_0015, g32p_row21_traceSegment_056_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_056 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_056 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_056_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_056 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 941 15 16, g32p_row21_traceSegment_056_0941_0015, g32p_row21_traceSegment_056_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_056 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 911 30 31, g32p_row21_traceSegment_056_0911_0030, g32p_row21_traceSegment_056_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_056 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 850 61 61, g32p_row21_traceSegment_056_0850_0061, g32p_row21_traceSegment_056_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_056 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 729 121 122, g32p_row21_traceSegment_056_0729_0121, g32p_row21_traceSegment_056_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_056 486 486 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 486 243 243, g32p_row21_traceSegment_056_0486_0243, g32p_row21_traceSegment_056_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_056_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_056 0 972 = [3, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_056 0 486 486, g32p_row21_traceSegment_056_0000_0486, g32p_row21_traceSegment_056_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 56 = [3, 0, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_056_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_059 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 59 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_059_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 0 15 15, g32p_row21_traceSegment_059_0000_0015, g32p_row21_traceSegment_059_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 30 15 15, g32p_row21_traceSegment_059_0030_0015, g32p_row21_traceSegment_059_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_059 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 0 30 30, g32p_row21_traceSegment_059_0000_0030, g32p_row21_traceSegment_059_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 60 15 15, g32p_row21_traceSegment_059_0060_0015, g32p_row21_traceSegment_059_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 90 15 16, g32p_row21_traceSegment_059_0090_0015, g32p_row21_traceSegment_059_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 60 30 31, g32p_row21_traceSegment_059_0060_0030, g32p_row21_traceSegment_059_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_059 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 0 60 61, g32p_row21_traceSegment_059_0000_0060, g32p_row21_traceSegment_059_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 121 15 15, g32p_row21_traceSegment_059_0121_0015, g32p_row21_traceSegment_059_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 151 15 16, g32p_row21_traceSegment_059_0151_0015, g32p_row21_traceSegment_059_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 121 30 31, g32p_row21_traceSegment_059_0121_0030, g32p_row21_traceSegment_059_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 182 15 15, g32p_row21_traceSegment_059_0182_0015, g32p_row21_traceSegment_059_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 227 16 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 212 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 212 15 16, g32p_row21_traceSegment_059_0212_0015, g32p_row21_traceSegment_059_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 182 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 182 30 31, g32p_row21_traceSegment_059_0182_0030, g32p_row21_traceSegment_059_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_059 121 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 121 61 61, g32p_row21_traceSegment_059_0121_0061, g32p_row21_traceSegment_059_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_059 0 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 0 121 122, g32p_row21_traceSegment_059_0000_0121, g32p_row21_traceSegment_059_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 243 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 258 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 243 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 243 15 15, g32p_row21_traceSegment_059_0243_0015, g32p_row21_traceSegment_059_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 288 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 273 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 273 15 15, g32p_row21_traceSegment_059_0273_0015, g32p_row21_traceSegment_059_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_059 243 60 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 243 30 30, g32p_row21_traceSegment_059_0243_0030, g32p_row21_traceSegment_059_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 303 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 318 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 303 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 303 15 15, g32p_row21_traceSegment_059_0303_0015, g32p_row21_traceSegment_059_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 333 15 16, g32p_row21_traceSegment_059_0333_0015, g32p_row21_traceSegment_059_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 303 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 303 30 31, g32p_row21_traceSegment_059_0303_0030, g32p_row21_traceSegment_059_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_059 243 121 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 243 60 61, g32p_row21_traceSegment_059_0243_0060, g32p_row21_traceSegment_059_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 364 15 15, g32p_row21_traceSegment_059_0364_0015, g32p_row21_traceSegment_059_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 394 15 16, g32p_row21_traceSegment_059_0394_0015, g32p_row21_traceSegment_059_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 364 30 31, g32p_row21_traceSegment_059_0364_0030, g32p_row21_traceSegment_059_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 440 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 425 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 425 15 15, g32p_row21_traceSegment_059_0425_0015, g32p_row21_traceSegment_059_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 455 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 470 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 455 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 455 15 16, g32p_row21_traceSegment_059_0455_0015, g32p_row21_traceSegment_059_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 425 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 425 30 31, g32p_row21_traceSegment_059_0425_0030, g32p_row21_traceSegment_059_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_059 364 122 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 364 61 61, g32p_row21_traceSegment_059_0364_0061, g32p_row21_traceSegment_059_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_059 243 243 = [10] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 243 121 122, g32p_row21_traceSegment_059_0243_0121, g32p_row21_traceSegment_059_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_059 0 486 = [12] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 0 243 243, g32p_row21_traceSegment_059_0000_0243, g32p_row21_traceSegment_059_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 486 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 501 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 486 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 486 15 15, g32p_row21_traceSegment_059_0486_0015, g32p_row21_traceSegment_059_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 531 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 516 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 516 15 15, g32p_row21_traceSegment_059_0516_0015, g32p_row21_traceSegment_059_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_059 486 60 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 486 30 30, g32p_row21_traceSegment_059_0486_0030, g32p_row21_traceSegment_059_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 546 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 546 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 546 15 15, g32p_row21_traceSegment_059_0546_0015, g32p_row21_traceSegment_059_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 576 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 576 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 576 15 16, g32p_row21_traceSegment_059_0576_0015, g32p_row21_traceSegment_059_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 546 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 546 30 31, g32p_row21_traceSegment_059_0546_0030, g32p_row21_traceSegment_059_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_059 486 121 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 486 60 61, g32p_row21_traceSegment_059_0486_0060, g32p_row21_traceSegment_059_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 607 15 15, g32p_row21_traceSegment_059_0607_0015, g32p_row21_traceSegment_059_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 637 15 16, g32p_row21_traceSegment_059_0637_0015, g32p_row21_traceSegment_059_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 607 30 31, g32p_row21_traceSegment_059_0607_0030, g32p_row21_traceSegment_059_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 668 15 15, g32p_row21_traceSegment_059_0668_0015, g32p_row21_traceSegment_059_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 698 15 16, g32p_row21_traceSegment_059_0698_0015, g32p_row21_traceSegment_059_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 668 30 31, g32p_row21_traceSegment_059_0668_0030, g32p_row21_traceSegment_059_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_059 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 607 61 61, g32p_row21_traceSegment_059_0607_0061, g32p_row21_traceSegment_059_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_059 486 243 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 486 121 122, g32p_row21_traceSegment_059_0486_0121, g32p_row21_traceSegment_059_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 729 15 15, g32p_row21_traceSegment_059_0729_0015, g32p_row21_traceSegment_059_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 759 15 15, g32p_row21_traceSegment_059_0759_0015, g32p_row21_traceSegment_059_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_059 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 729 30 30, g32p_row21_traceSegment_059_0729_0030, g32p_row21_traceSegment_059_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 789 15 15, g32p_row21_traceSegment_059_0789_0015, g32p_row21_traceSegment_059_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 819 15 16, g32p_row21_traceSegment_059_0819_0015, g32p_row21_traceSegment_059_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 789 30 31, g32p_row21_traceSegment_059_0789_0030, g32p_row21_traceSegment_059_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_059 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 729 60 61, g32p_row21_traceSegment_059_0729_0060, g32p_row21_traceSegment_059_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 850 15 15, g32p_row21_traceSegment_059_0850_0015, g32p_row21_traceSegment_059_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 880 15 16, g32p_row21_traceSegment_059_0880_0015, g32p_row21_traceSegment_059_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 850 30 31, g32p_row21_traceSegment_059_0850_0030, g32p_row21_traceSegment_059_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_059 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 911 15 15, g32p_row21_traceSegment_059_0911_0015, g32p_row21_traceSegment_059_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_059 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_059 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_059_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_059 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 941 15 16, g32p_row21_traceSegment_059_0941_0015, g32p_row21_traceSegment_059_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_059 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 911 30 31, g32p_row21_traceSegment_059_0911_0030, g32p_row21_traceSegment_059_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_059 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 850 61 61, g32p_row21_traceSegment_059_0850_0061, g32p_row21_traceSegment_059_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_059 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 729 121 122, g32p_row21_traceSegment_059_0729_0121, g32p_row21_traceSegment_059_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_059 486 486 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 486 243 243, g32p_row21_traceSegment_059_0486_0243, g32p_row21_traceSegment_059_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_059_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_059 0 972 = [18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_059 0 486 486, g32p_row21_traceSegment_059_0000_0486, g32p_row21_traceSegment_059_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 59 = [18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_059_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_062 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 62 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_062_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 0 15 15, g32p_row21_traceSegment_062_0000_0015, g32p_row21_traceSegment_062_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 30 15 15, g32p_row21_traceSegment_062_0030_0015, g32p_row21_traceSegment_062_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_062 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 0 30 30, g32p_row21_traceSegment_062_0000_0030, g32p_row21_traceSegment_062_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 60 15 15, g32p_row21_traceSegment_062_0060_0015, g32p_row21_traceSegment_062_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 90 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 105 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 90 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 90 15 16, g32p_row21_traceSegment_062_0090_0015, g32p_row21_traceSegment_062_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 60 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 60 30 31, g32p_row21_traceSegment_062_0060_0030, g32p_row21_traceSegment_062_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_062 0 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 0 60 61, g32p_row21_traceSegment_062_0000_0060, g32p_row21_traceSegment_062_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 121 15 15, g32p_row21_traceSegment_062_0121_0015, g32p_row21_traceSegment_062_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 151 15 16, g32p_row21_traceSegment_062_0151_0015, g32p_row21_traceSegment_062_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 121 30 31, g32p_row21_traceSegment_062_0121_0030, g32p_row21_traceSegment_062_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 182 15 15, g32p_row21_traceSegment_062_0182_0015, g32p_row21_traceSegment_062_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 212 15 16, g32p_row21_traceSegment_062_0212_0015, g32p_row21_traceSegment_062_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 182 30 31, g32p_row21_traceSegment_062_0182_0030, g32p_row21_traceSegment_062_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_062 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 121 61 61, g32p_row21_traceSegment_062_0121_0061, g32p_row21_traceSegment_062_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_062 0 243 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 0 121 122, g32p_row21_traceSegment_062_0000_0121, g32p_row21_traceSegment_062_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 243 15 15, g32p_row21_traceSegment_062_0243_0015, g32p_row21_traceSegment_062_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 273 15 15, g32p_row21_traceSegment_062_0273_0015, g32p_row21_traceSegment_062_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_062 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 243 30 30, g32p_row21_traceSegment_062_0243_0030, g32p_row21_traceSegment_062_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 318 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 303 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 303 15 15, g32p_row21_traceSegment_062_0303_0015, g32p_row21_traceSegment_062_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 333 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 348 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 333 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 333 15 16, g32p_row21_traceSegment_062_0333_0015, g32p_row21_traceSegment_062_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 303 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 303 30 31, g32p_row21_traceSegment_062_0303_0030, g32p_row21_traceSegment_062_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_062 243 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 243 60 61, g32p_row21_traceSegment_062_0243_0060, g32p_row21_traceSegment_062_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 364 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 379 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 364 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 364 15 15, g32p_row21_traceSegment_062_0364_0015, g32p_row21_traceSegment_062_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 394 15 16, g32p_row21_traceSegment_062_0394_0015, g32p_row21_traceSegment_062_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 364 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 364 30 31, g32p_row21_traceSegment_062_0364_0030, g32p_row21_traceSegment_062_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 425 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 425 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 425 15 15, g32p_row21_traceSegment_062_0425_0015, g32p_row21_traceSegment_062_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 455 15 16, g32p_row21_traceSegment_062_0455_0015, g32p_row21_traceSegment_062_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 425 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 425 30 31, g32p_row21_traceSegment_062_0425_0030, g32p_row21_traceSegment_062_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_062 364 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 364 61 61, g32p_row21_traceSegment_062_0364_0061, g32p_row21_traceSegment_062_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_062 243 243 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 243 121 122, g32p_row21_traceSegment_062_0243_0121, g32p_row21_traceSegment_062_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_062 0 486 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 0 243 243, g32p_row21_traceSegment_062_0000_0243, g32p_row21_traceSegment_062_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 501 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 486 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 486 15 15, g32p_row21_traceSegment_062_0486_0015, g32p_row21_traceSegment_062_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 516 15 15, g32p_row21_traceSegment_062_0516_0015, g32p_row21_traceSegment_062_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_062 486 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 486 30 30, g32p_row21_traceSegment_062_0486_0030, g32p_row21_traceSegment_062_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 546 15 15, g32p_row21_traceSegment_062_0546_0015, g32p_row21_traceSegment_062_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 576 15 16, g32p_row21_traceSegment_062_0576_0015, g32p_row21_traceSegment_062_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 546 30 31, g32p_row21_traceSegment_062_0546_0030, g32p_row21_traceSegment_062_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_062 486 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 486 60 61, g32p_row21_traceSegment_062_0486_0060, g32p_row21_traceSegment_062_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 607 15 15, g32p_row21_traceSegment_062_0607_0015, g32p_row21_traceSegment_062_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 637 15 16, g32p_row21_traceSegment_062_0637_0015, g32p_row21_traceSegment_062_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 607 30 31, g32p_row21_traceSegment_062_0607_0030, g32p_row21_traceSegment_062_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 668 15 15, g32p_row21_traceSegment_062_0668_0015, g32p_row21_traceSegment_062_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 713 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 698 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 698 15 16, g32p_row21_traceSegment_062_0698_0015, g32p_row21_traceSegment_062_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 668 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 668 30 31, g32p_row21_traceSegment_062_0668_0030, g32p_row21_traceSegment_062_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_062 607 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 607 61 61, g32p_row21_traceSegment_062_0607_0061, g32p_row21_traceSegment_062_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_062 486 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 486 121 122, g32p_row21_traceSegment_062_0486_0121, g32p_row21_traceSegment_062_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 744 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 729 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 729 15 15, g32p_row21_traceSegment_062_0729_0015, g32p_row21_traceSegment_062_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 759 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 759 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 759 15 15, g32p_row21_traceSegment_062_0759_0015, g32p_row21_traceSegment_062_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_062 729 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 729 30 30, g32p_row21_traceSegment_062_0729_0030, g32p_row21_traceSegment_062_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 789 15 15, g32p_row21_traceSegment_062_0789_0015, g32p_row21_traceSegment_062_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 819 15 16, g32p_row21_traceSegment_062_0819_0015, g32p_row21_traceSegment_062_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 789 30 31, g32p_row21_traceSegment_062_0789_0030, g32p_row21_traceSegment_062_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_062 729 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 729 60 61, g32p_row21_traceSegment_062_0729_0060, g32p_row21_traceSegment_062_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 865 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 850 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 850 15 15, g32p_row21_traceSegment_062_0850_0015, g32p_row21_traceSegment_062_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 880 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 880 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 880 15 16, g32p_row21_traceSegment_062_0880_0015, g32p_row21_traceSegment_062_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 850 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 850 30 31, g32p_row21_traceSegment_062_0850_0030, g32p_row21_traceSegment_062_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_062 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 911 15 15, g32p_row21_traceSegment_062_0911_0015, g32p_row21_traceSegment_062_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_062 941 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_062 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_062_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_062 941 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 941 15 16, g32p_row21_traceSegment_062_0941_0015, g32p_row21_traceSegment_062_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_062 911 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 911 30 31, g32p_row21_traceSegment_062_0911_0030, g32p_row21_traceSegment_062_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_062 850 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 850 61 61, g32p_row21_traceSegment_062_0850_0061, g32p_row21_traceSegment_062_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_062 729 243 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 729 121 122, g32p_row21_traceSegment_062_0729_0121, g32p_row21_traceSegment_062_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_062 486 486 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 486 243 243, g32p_row21_traceSegment_062_0486_0243, g32p_row21_traceSegment_062_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_062_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_062 0 972 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_062 0 486 486, g32p_row21_traceSegment_062_0000_0486, g32p_row21_traceSegment_062_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_062 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 62 = [0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_062_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_064 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 64 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_064_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 0 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 0 15 15, g32p_row21_traceSegment_064_0000_0015, g32p_row21_traceSegment_064_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 30 15 15, g32p_row21_traceSegment_064_0030_0015, g32p_row21_traceSegment_064_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_064 0 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 0 30 30, g32p_row21_traceSegment_064_0000_0030, g32p_row21_traceSegment_064_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 60 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 75 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 60 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 60 15 15, g32p_row21_traceSegment_064_0060_0015, g32p_row21_traceSegment_064_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 90 15 16, g32p_row21_traceSegment_064_0090_0015, g32p_row21_traceSegment_064_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 60 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 60 30 31, g32p_row21_traceSegment_064_0060_0030, g32p_row21_traceSegment_064_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_064 0 121 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 0 60 61, g32p_row21_traceSegment_064_0000_0060, g32p_row21_traceSegment_064_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 121 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 121 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 121 15 15, g32p_row21_traceSegment_064_0121_0015, g32p_row21_traceSegment_064_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 151 15 16, g32p_row21_traceSegment_064_0151_0015, g32p_row21_traceSegment_064_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 121 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 121 30 31, g32p_row21_traceSegment_064_0121_0030, g32p_row21_traceSegment_064_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 182 15 15, g32p_row21_traceSegment_064_0182_0015, g32p_row21_traceSegment_064_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 212 15 16, g32p_row21_traceSegment_064_0212_0015, g32p_row21_traceSegment_064_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 182 30 31, g32p_row21_traceSegment_064_0182_0030, g32p_row21_traceSegment_064_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_064 121 122 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 121 61 61, g32p_row21_traceSegment_064_0121_0061, g32p_row21_traceSegment_064_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_064 0 243 = [5, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 0 121 122, g32p_row21_traceSegment_064_0000_0121, g32p_row21_traceSegment_064_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 243 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 258 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 243 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 243 15 15, g32p_row21_traceSegment_064_0243_0015, g32p_row21_traceSegment_064_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 273 15 15, g32p_row21_traceSegment_064_0273_0015, g32p_row21_traceSegment_064_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_064 243 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 243 30 30, g32p_row21_traceSegment_064_0243_0030, g32p_row21_traceSegment_064_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 303 15 15, g32p_row21_traceSegment_064_0303_0015, g32p_row21_traceSegment_064_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 333 15 16, g32p_row21_traceSegment_064_0333_0015, g32p_row21_traceSegment_064_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 303 30 31, g32p_row21_traceSegment_064_0303_0030, g32p_row21_traceSegment_064_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_064 243 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 243 60 61, g32p_row21_traceSegment_064_0243_0060, g32p_row21_traceSegment_064_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 364 15 15, g32p_row21_traceSegment_064_0364_0015, g32p_row21_traceSegment_064_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 394 15 16, g32p_row21_traceSegment_064_0394_0015, g32p_row21_traceSegment_064_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 364 30 31, g32p_row21_traceSegment_064_0364_0030, g32p_row21_traceSegment_064_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 425 15 15, g32p_row21_traceSegment_064_0425_0015, g32p_row21_traceSegment_064_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 455 15 16, g32p_row21_traceSegment_064_0455_0015, g32p_row21_traceSegment_064_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 425 30 31, g32p_row21_traceSegment_064_0425_0030, g32p_row21_traceSegment_064_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_064 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 364 61 61, g32p_row21_traceSegment_064_0364_0061, g32p_row21_traceSegment_064_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_064 243 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 243 121 122, g32p_row21_traceSegment_064_0243_0121, g32p_row21_traceSegment_064_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_064 0 486 = [7, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 0 243 243, g32p_row21_traceSegment_064_0000_0243, g32p_row21_traceSegment_064_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 486 15 15, g32p_row21_traceSegment_064_0486_0015, g32p_row21_traceSegment_064_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 516 15 15, g32p_row21_traceSegment_064_0516_0015, g32p_row21_traceSegment_064_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_064 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 486 30 30, g32p_row21_traceSegment_064_0486_0030, g32p_row21_traceSegment_064_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 546 15 15, g32p_row21_traceSegment_064_0546_0015, g32p_row21_traceSegment_064_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 576 15 16, g32p_row21_traceSegment_064_0576_0015, g32p_row21_traceSegment_064_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 546 30 31, g32p_row21_traceSegment_064_0546_0030, g32p_row21_traceSegment_064_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_064 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 486 60 61, g32p_row21_traceSegment_064_0486_0060, g32p_row21_traceSegment_064_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 607 15 15, g32p_row21_traceSegment_064_0607_0015, g32p_row21_traceSegment_064_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 637 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 652 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 637 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 637 15 16, g32p_row21_traceSegment_064_0637_0015, g32p_row21_traceSegment_064_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 607 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 607 30 31, g32p_row21_traceSegment_064_0607_0030, g32p_row21_traceSegment_064_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 683 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 668 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 668 15 15, g32p_row21_traceSegment_064_0668_0015, g32p_row21_traceSegment_064_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 698 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 713 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 698 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 698 15 16, g32p_row21_traceSegment_064_0698_0015, g32p_row21_traceSegment_064_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 668 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 668 30 31, g32p_row21_traceSegment_064_0668_0030, g32p_row21_traceSegment_064_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_064 607 122 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 607 61 61, g32p_row21_traceSegment_064_0607_0061, g32p_row21_traceSegment_064_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_064 486 243 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 486 121 122, g32p_row21_traceSegment_064_0486_0121, g32p_row21_traceSegment_064_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 729 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 729 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 729 15 15, g32p_row21_traceSegment_064_0729_0015, g32p_row21_traceSegment_064_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 759 15 15, g32p_row21_traceSegment_064_0759_0015, g32p_row21_traceSegment_064_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_064 729 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 729 30 30, g32p_row21_traceSegment_064_0729_0030, g32p_row21_traceSegment_064_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 789 15 15, g32p_row21_traceSegment_064_0789_0015, g32p_row21_traceSegment_064_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 819 15 16, g32p_row21_traceSegment_064_0819_0015, g32p_row21_traceSegment_064_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 789 30 31, g32p_row21_traceSegment_064_0789_0030, g32p_row21_traceSegment_064_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_064 729 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 729 60 61, g32p_row21_traceSegment_064_0729_0060, g32p_row21_traceSegment_064_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 850 15 15, g32p_row21_traceSegment_064_0850_0015, g32p_row21_traceSegment_064_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 880 15 16, g32p_row21_traceSegment_064_0880_0015, g32p_row21_traceSegment_064_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 850 30 31, g32p_row21_traceSegment_064_0850_0030, g32p_row21_traceSegment_064_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_064 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 911 15 15, g32p_row21_traceSegment_064_0911_0015, g32p_row21_traceSegment_064_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_064 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_064 956 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_064_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_064 941 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 941 15 16, g32p_row21_traceSegment_064_0941_0015, g32p_row21_traceSegment_064_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_064 911 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 911 30 31, g32p_row21_traceSegment_064_0911_0030, g32p_row21_traceSegment_064_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_064 850 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 850 61 61, g32p_row21_traceSegment_064_0850_0061, g32p_row21_traceSegment_064_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_064 729 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 729 121 122, g32p_row21_traceSegment_064_0729_0121, g32p_row21_traceSegment_064_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_064 486 486 = [2, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 486 243 243, g32p_row21_traceSegment_064_0486_0243, g32p_row21_traceSegment_064_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_064_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_064 0 972 = [9, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_064 0 486 486, g32p_row21_traceSegment_064_0000_0486, g32p_row21_traceSegment_064_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 64 = [9, 0, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_064_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_065 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 65 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_065_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 0 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 0 15 15, g32p_row21_traceSegment_065_0000_0015, g32p_row21_traceSegment_065_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 30 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 30 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 30 15 15, g32p_row21_traceSegment_065_0030_0015, g32p_row21_traceSegment_065_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_065 0 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 0 30 30, g32p_row21_traceSegment_065_0000_0030, g32p_row21_traceSegment_065_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 60 15 15, g32p_row21_traceSegment_065_0060_0015, g32p_row21_traceSegment_065_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 90 15 16, g32p_row21_traceSegment_065_0090_0015, g32p_row21_traceSegment_065_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 60 30 31, g32p_row21_traceSegment_065_0060_0030, g32p_row21_traceSegment_065_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_065 0 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 0 60 61, g32p_row21_traceSegment_065_0000_0060, g32p_row21_traceSegment_065_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 121 15 15, g32p_row21_traceSegment_065_0121_0015, g32p_row21_traceSegment_065_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 151 15 16, g32p_row21_traceSegment_065_0151_0015, g32p_row21_traceSegment_065_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 121 30 31, g32p_row21_traceSegment_065_0121_0030, g32p_row21_traceSegment_065_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 182 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 182 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 182 15 15, g32p_row21_traceSegment_065_0182_0015, g32p_row21_traceSegment_065_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 212 15 16, g32p_row21_traceSegment_065_0212_0015, g32p_row21_traceSegment_065_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 182 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 182 30 31, g32p_row21_traceSegment_065_0182_0030, g32p_row21_traceSegment_065_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_065 121 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 121 61 61, g32p_row21_traceSegment_065_0121_0061, g32p_row21_traceSegment_065_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_065 0 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 0 121 122, g32p_row21_traceSegment_065_0000_0121, g32p_row21_traceSegment_065_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 243 15 15, g32p_row21_traceSegment_065_0243_0015, g32p_row21_traceSegment_065_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 273 15 15, g32p_row21_traceSegment_065_0273_0015, g32p_row21_traceSegment_065_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_065 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 243 30 30, g32p_row21_traceSegment_065_0243_0030, g32p_row21_traceSegment_065_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 303 15 15, g32p_row21_traceSegment_065_0303_0015, g32p_row21_traceSegment_065_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 333 15 16, g32p_row21_traceSegment_065_0333_0015, g32p_row21_traceSegment_065_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 303 30 31, g32p_row21_traceSegment_065_0303_0030, g32p_row21_traceSegment_065_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_065 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 243 60 61, g32p_row21_traceSegment_065_0243_0060, g32p_row21_traceSegment_065_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 379 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 364 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 364 15 15, g32p_row21_traceSegment_065_0364_0015, g32p_row21_traceSegment_065_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 409 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 394 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 394 15 16, g32p_row21_traceSegment_065_0394_0015, g32p_row21_traceSegment_065_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 364 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 364 30 31, g32p_row21_traceSegment_065_0364_0030, g32p_row21_traceSegment_065_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 425 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 425 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 425 15 15, g32p_row21_traceSegment_065_0425_0015, g32p_row21_traceSegment_065_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 470 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 455 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 455 15 16, g32p_row21_traceSegment_065_0455_0015, g32p_row21_traceSegment_065_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 425 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 425 30 31, g32p_row21_traceSegment_065_0425_0030, g32p_row21_traceSegment_065_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_065 364 122 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 364 61 61, g32p_row21_traceSegment_065_0364_0061, g32p_row21_traceSegment_065_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_065 243 243 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 243 121 122, g32p_row21_traceSegment_065_0243_0121, g32p_row21_traceSegment_065_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_065 0 486 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 0 243 243, g32p_row21_traceSegment_065_0000_0243, g32p_row21_traceSegment_065_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 501 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 486 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 486 15 15, g32p_row21_traceSegment_065_0486_0015, g32p_row21_traceSegment_065_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 516 15 15, g32p_row21_traceSegment_065_0516_0015, g32p_row21_traceSegment_065_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_065 486 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 486 30 30, g32p_row21_traceSegment_065_0486_0030, g32p_row21_traceSegment_065_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 546 15 15, g32p_row21_traceSegment_065_0546_0015, g32p_row21_traceSegment_065_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 576 15 16, g32p_row21_traceSegment_065_0576_0015, g32p_row21_traceSegment_065_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 546 30 31, g32p_row21_traceSegment_065_0546_0030, g32p_row21_traceSegment_065_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_065 486 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 486 60 61, g32p_row21_traceSegment_065_0486_0060, g32p_row21_traceSegment_065_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 607 15 15, g32p_row21_traceSegment_065_0607_0015, g32p_row21_traceSegment_065_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 637 15 16, g32p_row21_traceSegment_065_0637_0015, g32p_row21_traceSegment_065_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 607 30 31, g32p_row21_traceSegment_065_0607_0030, g32p_row21_traceSegment_065_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 683 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 668 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 668 15 15, g32p_row21_traceSegment_065_0668_0015, g32p_row21_traceSegment_065_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 698 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 698 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 698 15 16, g32p_row21_traceSegment_065_0698_0015, g32p_row21_traceSegment_065_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 668 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 668 30 31, g32p_row21_traceSegment_065_0668_0030, g32p_row21_traceSegment_065_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_065 607 122 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 607 61 61, g32p_row21_traceSegment_065_0607_0061, g32p_row21_traceSegment_065_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_065 486 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 486 121 122, g32p_row21_traceSegment_065_0486_0121, g32p_row21_traceSegment_065_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 744 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 729 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 729 15 15, g32p_row21_traceSegment_065_0729_0015, g32p_row21_traceSegment_065_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 774 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 759 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 759 15 15, g32p_row21_traceSegment_065_0759_0015, g32p_row21_traceSegment_065_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_065 729 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 729 30 30, g32p_row21_traceSegment_065_0729_0030, g32p_row21_traceSegment_065_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 789 15 15, g32p_row21_traceSegment_065_0789_0015, g32p_row21_traceSegment_065_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 819 15 16, g32p_row21_traceSegment_065_0819_0015, g32p_row21_traceSegment_065_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 789 30 31, g32p_row21_traceSegment_065_0789_0030, g32p_row21_traceSegment_065_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_065 729 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 729 60 61, g32p_row21_traceSegment_065_0729_0060, g32p_row21_traceSegment_065_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 865 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 850 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 850 15 15, g32p_row21_traceSegment_065_0850_0015, g32p_row21_traceSegment_065_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 880 15 16, g32p_row21_traceSegment_065_0880_0015, g32p_row21_traceSegment_065_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 850 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 850 30 31, g32p_row21_traceSegment_065_0850_0030, g32p_row21_traceSegment_065_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_065 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 911 15 15, g32p_row21_traceSegment_065_0911_0015, g32p_row21_traceSegment_065_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_065 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_065 956 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_065_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_065 941 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 941 15 16, g32p_row21_traceSegment_065_0941_0015, g32p_row21_traceSegment_065_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_065 911 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 911 30 31, g32p_row21_traceSegment_065_0911_0030, g32p_row21_traceSegment_065_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_065 850 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 850 61 61, g32p_row21_traceSegment_065_0850_0061, g32p_row21_traceSegment_065_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_065 729 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 729 121 122, g32p_row21_traceSegment_065_0729_0121, g32p_row21_traceSegment_065_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_065 486 486 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 486 243 243, g32p_row21_traceSegment_065_0486_0243, g32p_row21_traceSegment_065_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_065_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_065 0 972 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_065 0 486 486, g32p_row21_traceSegment_065_0000_0486, g32p_row21_traceSegment_065_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 65 = [0, 0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_065_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 51) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 51) (g32p_literalTraceValue 20 51)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_051]
  decide +kernel

theorem g32p_row21_tracePolynomial_053 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 53) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 53) (g32p_literalTraceValue 20 53)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_053]
  decide +kernel

theorem g32p_row21_tracePolynomial_054 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 54) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 54) (g32p_literalTraceValue 20 54)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_054]
  decide +kernel

theorem g32p_row21_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 56) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 56) (g32p_literalTraceValue 20 56)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row21_traceCoefficients_056]
  decide +kernel

theorem g32p_row21_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 59) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 59) (g32p_literalTraceValue 20 59)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_059]
  decide +kernel

theorem g32p_row21_tracePolynomial_062 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 62) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 62) (g32p_literalTraceValue 20 62)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_062]
  decide +kernel

theorem g32p_row21_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 64) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 64) (g32p_literalTraceValue 20 64)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_064]
  decide +kernel

theorem g32p_row21_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 65) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 65) (g32p_literalTraceValue 20 65)
      [1, 1, 1] [31104] = true := by
  rw [g32p_row21_traceCoefficients_065]
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

private def g32p_row21_traceSegment_066 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 66 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_066_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 0 15 15, g32p_row21_traceSegment_066_0000_0015, g32p_row21_traceSegment_066_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 30 15 15, g32p_row21_traceSegment_066_0030_0015, g32p_row21_traceSegment_066_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_066 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 0 30 30, g32p_row21_traceSegment_066_0000_0030, g32p_row21_traceSegment_066_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 60 15 15, g32p_row21_traceSegment_066_0060_0015, g32p_row21_traceSegment_066_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 90 15 16, g32p_row21_traceSegment_066_0090_0015, g32p_row21_traceSegment_066_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 60 30 31, g32p_row21_traceSegment_066_0060_0030, g32p_row21_traceSegment_066_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_066 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 0 60 61, g32p_row21_traceSegment_066_0000_0060, g32p_row21_traceSegment_066_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 121 15 15, g32p_row21_traceSegment_066_0121_0015, g32p_row21_traceSegment_066_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 151 15 16, g32p_row21_traceSegment_066_0151_0015, g32p_row21_traceSegment_066_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 121 30 31, g32p_row21_traceSegment_066_0121_0030, g32p_row21_traceSegment_066_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 197 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 182 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 182 15 15, g32p_row21_traceSegment_066_0182_0015, g32p_row21_traceSegment_066_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 212 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 227 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 212 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 212 15 16, g32p_row21_traceSegment_066_0212_0015, g32p_row21_traceSegment_066_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 182 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 182 30 31, g32p_row21_traceSegment_066_0182_0030, g32p_row21_traceSegment_066_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_066 121 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 121 61 61, g32p_row21_traceSegment_066_0121_0061, g32p_row21_traceSegment_066_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_066 0 243 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 0 121 122, g32p_row21_traceSegment_066_0000_0121, g32p_row21_traceSegment_066_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 243 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 243 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 243 15 15, g32p_row21_traceSegment_066_0243_0015, g32p_row21_traceSegment_066_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 273 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 288 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 273 30 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 273 15 15, g32p_row21_traceSegment_066_0273_0015, g32p_row21_traceSegment_066_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_066 243 60 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 243 30 30, g32p_row21_traceSegment_066_0243_0030, g32p_row21_traceSegment_066_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 303 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 318 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 303 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 303 15 15, g32p_row21_traceSegment_066_0303_0015, g32p_row21_traceSegment_066_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 333 15 16, g32p_row21_traceSegment_066_0333_0015, g32p_row21_traceSegment_066_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 303 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 303 30 31, g32p_row21_traceSegment_066_0303_0030, g32p_row21_traceSegment_066_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_066 243 121 = [5, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 243 60 61, g32p_row21_traceSegment_066_0243_0060, g32p_row21_traceSegment_066_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 364 15 15, g32p_row21_traceSegment_066_0364_0015, g32p_row21_traceSegment_066_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 394 15 16, g32p_row21_traceSegment_066_0394_0015, g32p_row21_traceSegment_066_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 364 30 31, g32p_row21_traceSegment_066_0364_0030, g32p_row21_traceSegment_066_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 425 15 15, g32p_row21_traceSegment_066_0425_0015, g32p_row21_traceSegment_066_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 455 15 16, g32p_row21_traceSegment_066_0455_0015, g32p_row21_traceSegment_066_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 425 30 31, g32p_row21_traceSegment_066_0425_0030, g32p_row21_traceSegment_066_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_066 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 364 61 61, g32p_row21_traceSegment_066_0364_0061, g32p_row21_traceSegment_066_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_066 243 243 = [5, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 243 121 122, g32p_row21_traceSegment_066_0243_0121, g32p_row21_traceSegment_066_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_066 0 486 = [5, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 0 243 243, g32p_row21_traceSegment_066_0000_0243, g32p_row21_traceSegment_066_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 486 15 15, g32p_row21_traceSegment_066_0486_0015, g32p_row21_traceSegment_066_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 516 15 15, g32p_row21_traceSegment_066_0516_0015, g32p_row21_traceSegment_066_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_066 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 486 30 30, g32p_row21_traceSegment_066_0486_0030, g32p_row21_traceSegment_066_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 546 15 15, g32p_row21_traceSegment_066_0546_0015, g32p_row21_traceSegment_066_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 591 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 576 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 576 15 16, g32p_row21_traceSegment_066_0576_0015, g32p_row21_traceSegment_066_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 546 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 546 30 31, g32p_row21_traceSegment_066_0546_0030, g32p_row21_traceSegment_066_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_066 486 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 486 60 61, g32p_row21_traceSegment_066_0486_0060, g32p_row21_traceSegment_066_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 622 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 607 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 607 15 15, g32p_row21_traceSegment_066_0607_0015, g32p_row21_traceSegment_066_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 637 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 652 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 637 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 637 15 16, g32p_row21_traceSegment_066_0637_0015, g32p_row21_traceSegment_066_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 607 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 607 30 31, g32p_row21_traceSegment_066_0607_0030, g32p_row21_traceSegment_066_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 668 15 15, g32p_row21_traceSegment_066_0668_0015, g32p_row21_traceSegment_066_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 698 15 16, g32p_row21_traceSegment_066_0698_0015, g32p_row21_traceSegment_066_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 668 30 31, g32p_row21_traceSegment_066_0668_0030, g32p_row21_traceSegment_066_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_066 607 122 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 607 61 61, g32p_row21_traceSegment_066_0607_0061, g32p_row21_traceSegment_066_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_066 486 243 = [3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 486 121 122, g32p_row21_traceSegment_066_0486_0121, g32p_row21_traceSegment_066_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 729 15 15, g32p_row21_traceSegment_066_0729_0015, g32p_row21_traceSegment_066_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 759 15 15, g32p_row21_traceSegment_066_0759_0015, g32p_row21_traceSegment_066_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_066 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 729 30 30, g32p_row21_traceSegment_066_0729_0030, g32p_row21_traceSegment_066_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 789 15 15, g32p_row21_traceSegment_066_0789_0015, g32p_row21_traceSegment_066_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 819 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 819 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 819 15 16, g32p_row21_traceSegment_066_0819_0015, g32p_row21_traceSegment_066_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 789 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 789 30 31, g32p_row21_traceSegment_066_0789_0030, g32p_row21_traceSegment_066_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_066 729 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 729 60 61, g32p_row21_traceSegment_066_0729_0060, g32p_row21_traceSegment_066_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 850 15 15, g32p_row21_traceSegment_066_0850_0015, g32p_row21_traceSegment_066_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 880 15 16, g32p_row21_traceSegment_066_0880_0015, g32p_row21_traceSegment_066_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 850 30 31, g32p_row21_traceSegment_066_0850_0030, g32p_row21_traceSegment_066_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 911 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 926 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_066 911 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 911 15 15, g32p_row21_traceSegment_066_0911_0015, g32p_row21_traceSegment_066_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_066 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_066 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_066_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_066 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 941 15 16, g32p_row21_traceSegment_066_0941_0015, g32p_row21_traceSegment_066_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_066 911 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 911 30 31, g32p_row21_traceSegment_066_0911_0030, g32p_row21_traceSegment_066_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_066 850 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 850 61 61, g32p_row21_traceSegment_066_0850_0061, g32p_row21_traceSegment_066_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_066 729 243 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 729 121 122, g32p_row21_traceSegment_066_0729_0121, g32p_row21_traceSegment_066_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_066 486 486 = [4, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 486 243 243, g32p_row21_traceSegment_066_0486_0243, g32p_row21_traceSegment_066_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_066_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_066 0 972 = [9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_066 0 486 486, g32p_row21_traceSegment_066_0000_0486, g32p_row21_traceSegment_066_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 66 = [9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_066_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_067 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 67 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_067_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 15 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 0 15 15, g32p_row21_traceSegment_067_0000_0015, g32p_row21_traceSegment_067_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 30 15 15, g32p_row21_traceSegment_067_0030_0015, g32p_row21_traceSegment_067_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_067 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 0 30 30, g32p_row21_traceSegment_067_0000_0030, g32p_row21_traceSegment_067_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 60 15 15, g32p_row21_traceSegment_067_0060_0015, g32p_row21_traceSegment_067_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 90 15 16, g32p_row21_traceSegment_067_0090_0015, g32p_row21_traceSegment_067_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 60 30 31, g32p_row21_traceSegment_067_0060_0030, g32p_row21_traceSegment_067_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_067 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 0 60 61, g32p_row21_traceSegment_067_0000_0060, g32p_row21_traceSegment_067_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 121 15 15, g32p_row21_traceSegment_067_0121_0015, g32p_row21_traceSegment_067_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 151 15 16, g32p_row21_traceSegment_067_0151_0015, g32p_row21_traceSegment_067_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 121 30 31, g32p_row21_traceSegment_067_0121_0030, g32p_row21_traceSegment_067_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 182 15 15, g32p_row21_traceSegment_067_0182_0015, g32p_row21_traceSegment_067_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 212 15 16, g32p_row21_traceSegment_067_0212_0015, g32p_row21_traceSegment_067_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 182 30 31, g32p_row21_traceSegment_067_0182_0030, g32p_row21_traceSegment_067_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_067 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 121 61 61, g32p_row21_traceSegment_067_0121_0061, g32p_row21_traceSegment_067_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_067 0 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 0 121 122, g32p_row21_traceSegment_067_0000_0121, g32p_row21_traceSegment_067_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 243 15 15, g32p_row21_traceSegment_067_0243_0015, g32p_row21_traceSegment_067_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 273 15 15, g32p_row21_traceSegment_067_0273_0015, g32p_row21_traceSegment_067_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_067 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 243 30 30, g32p_row21_traceSegment_067_0243_0030, g32p_row21_traceSegment_067_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 303 15 15, g32p_row21_traceSegment_067_0303_0015, g32p_row21_traceSegment_067_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 333 15 16, g32p_row21_traceSegment_067_0333_0015, g32p_row21_traceSegment_067_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 303 30 31, g32p_row21_traceSegment_067_0303_0030, g32p_row21_traceSegment_067_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_067 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 243 60 61, g32p_row21_traceSegment_067_0243_0060, g32p_row21_traceSegment_067_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 364 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 379 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 364 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 364 15 15, g32p_row21_traceSegment_067_0364_0015, g32p_row21_traceSegment_067_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 394 15 16, g32p_row21_traceSegment_067_0394_0015, g32p_row21_traceSegment_067_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 364 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 364 30 31, g32p_row21_traceSegment_067_0364_0030, g32p_row21_traceSegment_067_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 425 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 425 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 425 15 15, g32p_row21_traceSegment_067_0425_0015, g32p_row21_traceSegment_067_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 455 15 16, g32p_row21_traceSegment_067_0455_0015, g32p_row21_traceSegment_067_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 425 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 425 30 31, g32p_row21_traceSegment_067_0425_0030, g32p_row21_traceSegment_067_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_067 364 122 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 364 61 61, g32p_row21_traceSegment_067_0364_0061, g32p_row21_traceSegment_067_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_067 243 243 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 243 121 122, g32p_row21_traceSegment_067_0243_0121, g32p_row21_traceSegment_067_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_067 0 486 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 0 243 243, g32p_row21_traceSegment_067_0000_0243, g32p_row21_traceSegment_067_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 486 15 15, g32p_row21_traceSegment_067_0486_0015, g32p_row21_traceSegment_067_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 516 15 15, g32p_row21_traceSegment_067_0516_0015, g32p_row21_traceSegment_067_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_067 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 486 30 30, g32p_row21_traceSegment_067_0486_0030, g32p_row21_traceSegment_067_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 546 15 15, g32p_row21_traceSegment_067_0546_0015, g32p_row21_traceSegment_067_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 576 15 16, g32p_row21_traceSegment_067_0576_0015, g32p_row21_traceSegment_067_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 546 30 31, g32p_row21_traceSegment_067_0546_0030, g32p_row21_traceSegment_067_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_067 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 486 60 61, g32p_row21_traceSegment_067_0486_0060, g32p_row21_traceSegment_067_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 607 15 15, g32p_row21_traceSegment_067_0607_0015, g32p_row21_traceSegment_067_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 637 15 16, g32p_row21_traceSegment_067_0637_0015, g32p_row21_traceSegment_067_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 607 30 31, g32p_row21_traceSegment_067_0607_0030, g32p_row21_traceSegment_067_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 668 15 15, g32p_row21_traceSegment_067_0668_0015, g32p_row21_traceSegment_067_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 698 15 16, g32p_row21_traceSegment_067_0698_0015, g32p_row21_traceSegment_067_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 668 30 31, g32p_row21_traceSegment_067_0668_0030, g32p_row21_traceSegment_067_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_067 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 607 61 61, g32p_row21_traceSegment_067_0607_0061, g32p_row21_traceSegment_067_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_067 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 486 121 122, g32p_row21_traceSegment_067_0486_0121, g32p_row21_traceSegment_067_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 729 15 15, g32p_row21_traceSegment_067_0729_0015, g32p_row21_traceSegment_067_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 759 15 15, g32p_row21_traceSegment_067_0759_0015, g32p_row21_traceSegment_067_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_067 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 729 30 30, g32p_row21_traceSegment_067_0729_0030, g32p_row21_traceSegment_067_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 789 15 15, g32p_row21_traceSegment_067_0789_0015, g32p_row21_traceSegment_067_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 819 15 16, g32p_row21_traceSegment_067_0819_0015, g32p_row21_traceSegment_067_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 789 30 31, g32p_row21_traceSegment_067_0789_0030, g32p_row21_traceSegment_067_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_067 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 729 60 61, g32p_row21_traceSegment_067_0729_0060, g32p_row21_traceSegment_067_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 850 15 15, g32p_row21_traceSegment_067_0850_0015, g32p_row21_traceSegment_067_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 880 15 16, g32p_row21_traceSegment_067_0880_0015, g32p_row21_traceSegment_067_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 850 30 31, g32p_row21_traceSegment_067_0850_0030, g32p_row21_traceSegment_067_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_067 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 911 15 15, g32p_row21_traceSegment_067_0911_0015, g32p_row21_traceSegment_067_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_067 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_067 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_067_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_067 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 941 15 16, g32p_row21_traceSegment_067_0941_0015, g32p_row21_traceSegment_067_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_067 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 911 30 31, g32p_row21_traceSegment_067_0911_0030, g32p_row21_traceSegment_067_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_067 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 850 61 61, g32p_row21_traceSegment_067_0850_0061, g32p_row21_traceSegment_067_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_067 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 729 121 122, g32p_row21_traceSegment_067_0729_0121, g32p_row21_traceSegment_067_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_067 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 486 243 243, g32p_row21_traceSegment_067_0486_0243, g32p_row21_traceSegment_067_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_067_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_067 0 972 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_067 0 486 486, g32p_row21_traceSegment_067_0000_0486, g32p_row21_traceSegment_067_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 67 = [1, 0, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_067_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_068 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 68 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_068_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 0 15 15, g32p_row21_traceSegment_068_0000_0015, g32p_row21_traceSegment_068_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 30 15 15, g32p_row21_traceSegment_068_0030_0015, g32p_row21_traceSegment_068_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_068 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 0 30 30, g32p_row21_traceSegment_068_0000_0030, g32p_row21_traceSegment_068_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 60 15 15, g32p_row21_traceSegment_068_0060_0015, g32p_row21_traceSegment_068_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 90 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 105 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 90 31 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 90 15 16, g32p_row21_traceSegment_068_0090_0015, g32p_row21_traceSegment_068_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 60 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 60 30 31, g32p_row21_traceSegment_068_0060_0030, g32p_row21_traceSegment_068_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_068 0 121 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 0 60 61, g32p_row21_traceSegment_068_0000_0060, g32p_row21_traceSegment_068_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 121 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 136 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 121 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 121 15 15, g32p_row21_traceSegment_068_0121_0015, g32p_row21_traceSegment_068_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 151 15 16, g32p_row21_traceSegment_068_0151_0015, g32p_row21_traceSegment_068_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 121 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 121 30 31, g32p_row21_traceSegment_068_0121_0030, g32p_row21_traceSegment_068_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 182 15 15, g32p_row21_traceSegment_068_0182_0015, g32p_row21_traceSegment_068_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 212 15 16, g32p_row21_traceSegment_068_0212_0015, g32p_row21_traceSegment_068_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 182 30 31, g32p_row21_traceSegment_068_0182_0030, g32p_row21_traceSegment_068_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_068 121 122 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 121 61 61, g32p_row21_traceSegment_068_0121_0061, g32p_row21_traceSegment_068_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_068 0 243 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 0 121 122, g32p_row21_traceSegment_068_0000_0121, g32p_row21_traceSegment_068_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 243 15 15, g32p_row21_traceSegment_068_0243_0015, g32p_row21_traceSegment_068_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 273 15 15, g32p_row21_traceSegment_068_0273_0015, g32p_row21_traceSegment_068_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_068 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 243 30 30, g32p_row21_traceSegment_068_0243_0030, g32p_row21_traceSegment_068_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 303 15 15, g32p_row21_traceSegment_068_0303_0015, g32p_row21_traceSegment_068_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 333 15 16, g32p_row21_traceSegment_068_0333_0015, g32p_row21_traceSegment_068_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 303 30 31, g32p_row21_traceSegment_068_0303_0030, g32p_row21_traceSegment_068_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_068 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 243 60 61, g32p_row21_traceSegment_068_0243_0060, g32p_row21_traceSegment_068_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 364 15 15, g32p_row21_traceSegment_068_0364_0015, g32p_row21_traceSegment_068_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 394 15 16, g32p_row21_traceSegment_068_0394_0015, g32p_row21_traceSegment_068_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 364 30 31, g32p_row21_traceSegment_068_0364_0030, g32p_row21_traceSegment_068_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 425 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 425 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 425 15 15, g32p_row21_traceSegment_068_0425_0015, g32p_row21_traceSegment_068_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 455 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 455 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 455 15 16, g32p_row21_traceSegment_068_0455_0015, g32p_row21_traceSegment_068_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 425 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 425 30 31, g32p_row21_traceSegment_068_0425_0030, g32p_row21_traceSegment_068_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_068 364 122 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 364 61 61, g32p_row21_traceSegment_068_0364_0061, g32p_row21_traceSegment_068_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_068 243 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 243 121 122, g32p_row21_traceSegment_068_0243_0121, g32p_row21_traceSegment_068_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_068 0 486 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 0 243 243, g32p_row21_traceSegment_068_0000_0243, g32p_row21_traceSegment_068_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 501 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 486 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 486 15 15, g32p_row21_traceSegment_068_0486_0015, g32p_row21_traceSegment_068_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 516 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 516 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 516 15 15, g32p_row21_traceSegment_068_0516_0015, g32p_row21_traceSegment_068_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_068 486 60 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 486 30 30, g32p_row21_traceSegment_068_0486_0030, g32p_row21_traceSegment_068_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 561 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 546 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 546 15 15, g32p_row21_traceSegment_068_0546_0015, g32p_row21_traceSegment_068_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 576 15 16, g32p_row21_traceSegment_068_0576_0015, g32p_row21_traceSegment_068_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 546 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 546 30 31, g32p_row21_traceSegment_068_0546_0030, g32p_row21_traceSegment_068_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_068 486 121 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 486 60 61, g32p_row21_traceSegment_068_0486_0060, g32p_row21_traceSegment_068_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 607 15 15, g32p_row21_traceSegment_068_0607_0015, g32p_row21_traceSegment_068_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 637 15 16, g32p_row21_traceSegment_068_0637_0015, g32p_row21_traceSegment_068_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 607 30 31, g32p_row21_traceSegment_068_0607_0030, g32p_row21_traceSegment_068_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 668 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 668 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 668 15 15, g32p_row21_traceSegment_068_0668_0015, g32p_row21_traceSegment_068_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 698 15 16, g32p_row21_traceSegment_068_0698_0015, g32p_row21_traceSegment_068_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 668 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 668 30 31, g32p_row21_traceSegment_068_0668_0030, g32p_row21_traceSegment_068_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_068 607 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 607 61 61, g32p_row21_traceSegment_068_0607_0061, g32p_row21_traceSegment_068_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_068 486 243 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 486 121 122, g32p_row21_traceSegment_068_0486_0121, g32p_row21_traceSegment_068_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 729 15 15, g32p_row21_traceSegment_068_0729_0015, g32p_row21_traceSegment_068_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 759 15 15, g32p_row21_traceSegment_068_0759_0015, g32p_row21_traceSegment_068_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_068 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 729 30 30, g32p_row21_traceSegment_068_0729_0030, g32p_row21_traceSegment_068_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 789 15 15, g32p_row21_traceSegment_068_0789_0015, g32p_row21_traceSegment_068_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 819 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 819 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 819 15 16, g32p_row21_traceSegment_068_0819_0015, g32p_row21_traceSegment_068_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 789 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 789 30 31, g32p_row21_traceSegment_068_0789_0030, g32p_row21_traceSegment_068_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_068 729 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 729 60 61, g32p_row21_traceSegment_068_0729_0060, g32p_row21_traceSegment_068_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 850 15 15, g32p_row21_traceSegment_068_0850_0015, g32p_row21_traceSegment_068_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 880 15 16, g32p_row21_traceSegment_068_0880_0015, g32p_row21_traceSegment_068_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 850 30 31, g32p_row21_traceSegment_068_0850_0030, g32p_row21_traceSegment_068_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_068 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 911 15 15, g32p_row21_traceSegment_068_0911_0015, g32p_row21_traceSegment_068_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_068 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_068 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_068_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_068 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 941 15 16, g32p_row21_traceSegment_068_0941_0015, g32p_row21_traceSegment_068_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_068 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 911 30 31, g32p_row21_traceSegment_068_0911_0030, g32p_row21_traceSegment_068_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_068 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 850 61 61, g32p_row21_traceSegment_068_0850_0061, g32p_row21_traceSegment_068_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_068 729 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 729 121 122, g32p_row21_traceSegment_068_0729_0121, g32p_row21_traceSegment_068_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_068 486 486 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 486 243 243, g32p_row21_traceSegment_068_0486_0243, g32p_row21_traceSegment_068_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_068_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_068 0 972 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_068 0 486 486, g32p_row21_traceSegment_068_0000_0486, g32p_row21_traceSegment_068_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_068 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 68 = [0, 0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_068_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_070 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 70 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_070_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 0 15 15, g32p_row21_traceSegment_070_0000_0015, g32p_row21_traceSegment_070_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 30 15 15, g32p_row21_traceSegment_070_0030_0015, g32p_row21_traceSegment_070_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_070 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 0 30 30, g32p_row21_traceSegment_070_0000_0030, g32p_row21_traceSegment_070_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 60 15 15, g32p_row21_traceSegment_070_0060_0015, g32p_row21_traceSegment_070_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 90 15 16, g32p_row21_traceSegment_070_0090_0015, g32p_row21_traceSegment_070_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 60 30 31, g32p_row21_traceSegment_070_0060_0030, g32p_row21_traceSegment_070_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_070 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 0 60 61, g32p_row21_traceSegment_070_0000_0060, g32p_row21_traceSegment_070_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 121 15 15, g32p_row21_traceSegment_070_0121_0015, g32p_row21_traceSegment_070_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 151 15 16, g32p_row21_traceSegment_070_0151_0015, g32p_row21_traceSegment_070_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 121 30 31, g32p_row21_traceSegment_070_0121_0030, g32p_row21_traceSegment_070_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 197 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 182 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 182 15 15, g32p_row21_traceSegment_070_0182_0015, g32p_row21_traceSegment_070_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 212 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 227 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 212 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 212 15 16, g32p_row21_traceSegment_070_0212_0015, g32p_row21_traceSegment_070_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 182 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 182 30 31, g32p_row21_traceSegment_070_0182_0030, g32p_row21_traceSegment_070_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_070 121 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 121 61 61, g32p_row21_traceSegment_070_0121_0061, g32p_row21_traceSegment_070_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_070 0 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 0 121 122, g32p_row21_traceSegment_070_0000_0121, g32p_row21_traceSegment_070_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 243 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 258 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 243 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 243 15 15, g32p_row21_traceSegment_070_0243_0015, g32p_row21_traceSegment_070_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 273 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 288 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 273 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 273 15 15, g32p_row21_traceSegment_070_0273_0015, g32p_row21_traceSegment_070_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_070 243 60 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 243 30 30, g32p_row21_traceSegment_070_0243_0030, g32p_row21_traceSegment_070_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 303 15 15, g32p_row21_traceSegment_070_0303_0015, g32p_row21_traceSegment_070_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 333 15 16, g32p_row21_traceSegment_070_0333_0015, g32p_row21_traceSegment_070_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 303 30 31, g32p_row21_traceSegment_070_0303_0030, g32p_row21_traceSegment_070_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_070 243 121 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 243 60 61, g32p_row21_traceSegment_070_0243_0060, g32p_row21_traceSegment_070_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 364 15 15, g32p_row21_traceSegment_070_0364_0015, g32p_row21_traceSegment_070_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 394 15 16, g32p_row21_traceSegment_070_0394_0015, g32p_row21_traceSegment_070_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 364 30 31, g32p_row21_traceSegment_070_0364_0030, g32p_row21_traceSegment_070_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 425 15 15, g32p_row21_traceSegment_070_0425_0015, g32p_row21_traceSegment_070_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 455 15 16, g32p_row21_traceSegment_070_0455_0015, g32p_row21_traceSegment_070_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 425 30 31, g32p_row21_traceSegment_070_0425_0030, g32p_row21_traceSegment_070_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_070 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 364 61 61, g32p_row21_traceSegment_070_0364_0061, g32p_row21_traceSegment_070_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_070 243 243 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 243 121 122, g32p_row21_traceSegment_070_0243_0121, g32p_row21_traceSegment_070_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_070 0 486 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 0 243 243, g32p_row21_traceSegment_070_0000_0243, g32p_row21_traceSegment_070_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 486 15 15, g32p_row21_traceSegment_070_0486_0015, g32p_row21_traceSegment_070_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 516 15 15, g32p_row21_traceSegment_070_0516_0015, g32p_row21_traceSegment_070_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_070 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 486 30 30, g32p_row21_traceSegment_070_0486_0030, g32p_row21_traceSegment_070_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 546 15 15, g32p_row21_traceSegment_070_0546_0015, g32p_row21_traceSegment_070_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 576 15 16, g32p_row21_traceSegment_070_0576_0015, g32p_row21_traceSegment_070_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 546 30 31, g32p_row21_traceSegment_070_0546_0030, g32p_row21_traceSegment_070_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_070 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 486 60 61, g32p_row21_traceSegment_070_0486_0060, g32p_row21_traceSegment_070_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 607 15 15, g32p_row21_traceSegment_070_0607_0015, g32p_row21_traceSegment_070_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 637 15 16, g32p_row21_traceSegment_070_0637_0015, g32p_row21_traceSegment_070_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 607 30 31, g32p_row21_traceSegment_070_0607_0030, g32p_row21_traceSegment_070_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 668 15 15, g32p_row21_traceSegment_070_0668_0015, g32p_row21_traceSegment_070_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 698 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 698 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 698 15 16, g32p_row21_traceSegment_070_0698_0015, g32p_row21_traceSegment_070_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 668 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 668 30 31, g32p_row21_traceSegment_070_0668_0030, g32p_row21_traceSegment_070_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_070 607 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 607 61 61, g32p_row21_traceSegment_070_0607_0061, g32p_row21_traceSegment_070_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_070 486 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 486 121 122, g32p_row21_traceSegment_070_0486_0121, g32p_row21_traceSegment_070_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 729 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 729 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 729 15 15, g32p_row21_traceSegment_070_0729_0015, g32p_row21_traceSegment_070_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 774 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 759 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 759 15 15, g32p_row21_traceSegment_070_0759_0015, g32p_row21_traceSegment_070_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_070 729 60 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 729 30 30, g32p_row21_traceSegment_070_0729_0030, g32p_row21_traceSegment_070_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 789 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 789 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 789 15 15, g32p_row21_traceSegment_070_0789_0015, g32p_row21_traceSegment_070_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 819 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 819 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 819 15 16, g32p_row21_traceSegment_070_0819_0015, g32p_row21_traceSegment_070_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 789 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 789 30 31, g32p_row21_traceSegment_070_0789_0030, g32p_row21_traceSegment_070_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_070 729 121 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 729 60 61, g32p_row21_traceSegment_070_0729_0060, g32p_row21_traceSegment_070_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 850 15 15, g32p_row21_traceSegment_070_0850_0015, g32p_row21_traceSegment_070_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 880 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 880 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 880 15 16, g32p_row21_traceSegment_070_0880_0015, g32p_row21_traceSegment_070_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 850 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 850 30 31, g32p_row21_traceSegment_070_0850_0030, g32p_row21_traceSegment_070_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_070 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 911 15 15, g32p_row21_traceSegment_070_0911_0015, g32p_row21_traceSegment_070_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_070 941 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_070 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_070_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_070 941 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 941 15 16, g32p_row21_traceSegment_070_0941_0015, g32p_row21_traceSegment_070_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_070 911 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 911 30 31, g32p_row21_traceSegment_070_0911_0030, g32p_row21_traceSegment_070_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_070 850 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 850 61 61, g32p_row21_traceSegment_070_0850_0061, g32p_row21_traceSegment_070_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_070 729 243 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 729 121 122, g32p_row21_traceSegment_070_0729_0121, g32p_row21_traceSegment_070_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_070 486 486 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 486 243 243, g32p_row21_traceSegment_070_0486_0243, g32p_row21_traceSegment_070_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_070_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_070 0 972 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_070 0 486 486, g32p_row21_traceSegment_070_0000_0486, g32p_row21_traceSegment_070_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_070 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 70 = [0, 0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_070_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_071 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 71 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_071_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 0 15 15, g32p_row21_traceSegment_071_0000_0015, g32p_row21_traceSegment_071_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 30 15 15, g32p_row21_traceSegment_071_0030_0015, g32p_row21_traceSegment_071_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_071 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 0 30 30, g32p_row21_traceSegment_071_0000_0030, g32p_row21_traceSegment_071_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 60 15 15, g32p_row21_traceSegment_071_0060_0015, g32p_row21_traceSegment_071_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 90 15 16, g32p_row21_traceSegment_071_0090_0015, g32p_row21_traceSegment_071_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 60 30 31, g32p_row21_traceSegment_071_0060_0030, g32p_row21_traceSegment_071_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_071 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 0 60 61, g32p_row21_traceSegment_071_0000_0060, g32p_row21_traceSegment_071_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 121 15 15, g32p_row21_traceSegment_071_0121_0015, g32p_row21_traceSegment_071_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 166 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 151 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 151 15 16, g32p_row21_traceSegment_071_0151_0015, g32p_row21_traceSegment_071_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 121 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 121 30 31, g32p_row21_traceSegment_071_0121_0030, g32p_row21_traceSegment_071_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 182 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 197 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 182 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 182 15 15, g32p_row21_traceSegment_071_0182_0015, g32p_row21_traceSegment_071_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 212 15 16, g32p_row21_traceSegment_071_0212_0015, g32p_row21_traceSegment_071_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 182 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 182 30 31, g32p_row21_traceSegment_071_0182_0030, g32p_row21_traceSegment_071_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_071 121 122 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 121 61 61, g32p_row21_traceSegment_071_0121_0061, g32p_row21_traceSegment_071_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_071 0 243 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 0 121 122, g32p_row21_traceSegment_071_0000_0121, g32p_row21_traceSegment_071_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 243 15 15, g32p_row21_traceSegment_071_0243_0015, g32p_row21_traceSegment_071_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 273 15 15, g32p_row21_traceSegment_071_0273_0015, g32p_row21_traceSegment_071_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_071 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 243 30 30, g32p_row21_traceSegment_071_0243_0030, g32p_row21_traceSegment_071_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 303 15 15, g32p_row21_traceSegment_071_0303_0015, g32p_row21_traceSegment_071_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 333 15 16, g32p_row21_traceSegment_071_0333_0015, g32p_row21_traceSegment_071_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 303 30 31, g32p_row21_traceSegment_071_0303_0030, g32p_row21_traceSegment_071_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_071 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 243 60 61, g32p_row21_traceSegment_071_0243_0060, g32p_row21_traceSegment_071_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 364 15 15, g32p_row21_traceSegment_071_0364_0015, g32p_row21_traceSegment_071_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 409 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 394 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 394 15 16, g32p_row21_traceSegment_071_0394_0015, g32p_row21_traceSegment_071_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 364 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 364 30 31, g32p_row21_traceSegment_071_0364_0030, g32p_row21_traceSegment_071_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 440 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 425 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 425 15 15, g32p_row21_traceSegment_071_0425_0015, g32p_row21_traceSegment_071_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 470 16 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 455 31 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 455 15 16, g32p_row21_traceSegment_071_0455_0015, g32p_row21_traceSegment_071_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 425 61 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 425 30 31, g32p_row21_traceSegment_071_0425_0030, g32p_row21_traceSegment_071_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_071 364 122 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 364 61 61, g32p_row21_traceSegment_071_0364_0061, g32p_row21_traceSegment_071_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_071 243 243 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 243 121 122, g32p_row21_traceSegment_071_0243_0121, g32p_row21_traceSegment_071_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_071 0 486 = [0, 7, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 0 243 243, g32p_row21_traceSegment_071_0000_0243, g32p_row21_traceSegment_071_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 486 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 501 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 486 30 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 486 15 15, g32p_row21_traceSegment_071_0486_0015, g32p_row21_traceSegment_071_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 516 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 516 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 516 15 15, g32p_row21_traceSegment_071_0516_0015, g32p_row21_traceSegment_071_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_071 486 60 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 486 30 30, g32p_row21_traceSegment_071_0486_0030, g32p_row21_traceSegment_071_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 546 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 561 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 546 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 546 15 15, g32p_row21_traceSegment_071_0546_0015, g32p_row21_traceSegment_071_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 576 15 16, g32p_row21_traceSegment_071_0576_0015, g32p_row21_traceSegment_071_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 546 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 546 30 31, g32p_row21_traceSegment_071_0546_0030, g32p_row21_traceSegment_071_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_071 486 121 = [0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 486 60 61, g32p_row21_traceSegment_071_0486_0060, g32p_row21_traceSegment_071_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 607 15 15, g32p_row21_traceSegment_071_0607_0015, g32p_row21_traceSegment_071_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 637 15 16, g32p_row21_traceSegment_071_0637_0015, g32p_row21_traceSegment_071_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 607 30 31, g32p_row21_traceSegment_071_0607_0030, g32p_row21_traceSegment_071_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 668 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 668 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 668 15 15, g32p_row21_traceSegment_071_0668_0015, g32p_row21_traceSegment_071_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 698 15 16, g32p_row21_traceSegment_071_0698_0015, g32p_row21_traceSegment_071_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 668 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 668 30 31, g32p_row21_traceSegment_071_0668_0030, g32p_row21_traceSegment_071_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_071 607 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 607 61 61, g32p_row21_traceSegment_071_0607_0061, g32p_row21_traceSegment_071_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_071 486 243 = [0, 2, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 486 121 122, g32p_row21_traceSegment_071_0486_0121, g32p_row21_traceSegment_071_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 729 15 15, g32p_row21_traceSegment_071_0729_0015, g32p_row21_traceSegment_071_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 759 15 15, g32p_row21_traceSegment_071_0759_0015, g32p_row21_traceSegment_071_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_071 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 729 30 30, g32p_row21_traceSegment_071_0729_0030, g32p_row21_traceSegment_071_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 789 15 15, g32p_row21_traceSegment_071_0789_0015, g32p_row21_traceSegment_071_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 819 15 16, g32p_row21_traceSegment_071_0819_0015, g32p_row21_traceSegment_071_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 789 30 31, g32p_row21_traceSegment_071_0789_0030, g32p_row21_traceSegment_071_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_071 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 729 60 61, g32p_row21_traceSegment_071_0729_0060, g32p_row21_traceSegment_071_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 850 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 850 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 850 15 15, g32p_row21_traceSegment_071_0850_0015, g32p_row21_traceSegment_071_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 880 15 16, g32p_row21_traceSegment_071_0880_0015, g32p_row21_traceSegment_071_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 850 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 850 30 31, g32p_row21_traceSegment_071_0850_0030, g32p_row21_traceSegment_071_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_071 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 911 15 15, g32p_row21_traceSegment_071_0911_0015, g32p_row21_traceSegment_071_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_071 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_071 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_071_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_071 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 941 15 16, g32p_row21_traceSegment_071_0941_0015, g32p_row21_traceSegment_071_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_071 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 911 30 31, g32p_row21_traceSegment_071_0911_0030, g32p_row21_traceSegment_071_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_071 850 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 850 61 61, g32p_row21_traceSegment_071_0850_0061, g32p_row21_traceSegment_071_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_071 729 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 729 121 122, g32p_row21_traceSegment_071_0729_0121, g32p_row21_traceSegment_071_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_071 486 486 = [0, 2, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 486 243 243, g32p_row21_traceSegment_071_0486_0243, g32p_row21_traceSegment_071_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_071_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_071 0 972 = [0, 9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_071 0 486 486, g32p_row21_traceSegment_071_0000_0486, g32p_row21_traceSegment_071_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 71 = [0, 9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_071_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_074 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 74 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_074_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 0 15 15, g32p_row21_traceSegment_074_0000_0015, g32p_row21_traceSegment_074_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 30 15 15, g32p_row21_traceSegment_074_0030_0015, g32p_row21_traceSegment_074_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_074 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 0 30 30, g32p_row21_traceSegment_074_0000_0030, g32p_row21_traceSegment_074_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 60 15 15, g32p_row21_traceSegment_074_0060_0015, g32p_row21_traceSegment_074_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 90 15 16, g32p_row21_traceSegment_074_0090_0015, g32p_row21_traceSegment_074_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 60 30 31, g32p_row21_traceSegment_074_0060_0030, g32p_row21_traceSegment_074_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_074 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 0 60 61, g32p_row21_traceSegment_074_0000_0060, g32p_row21_traceSegment_074_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 121 15 15, g32p_row21_traceSegment_074_0121_0015, g32p_row21_traceSegment_074_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 166 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 151 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 151 15 16, g32p_row21_traceSegment_074_0151_0015, g32p_row21_traceSegment_074_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 121 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 121 30 31, g32p_row21_traceSegment_074_0121_0030, g32p_row21_traceSegment_074_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 182 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 182 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 182 15 15, g32p_row21_traceSegment_074_0182_0015, g32p_row21_traceSegment_074_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 212 15 16, g32p_row21_traceSegment_074_0212_0015, g32p_row21_traceSegment_074_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 182 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 182 30 31, g32p_row21_traceSegment_074_0182_0030, g32p_row21_traceSegment_074_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_074 121 122 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 121 61 61, g32p_row21_traceSegment_074_0121_0061, g32p_row21_traceSegment_074_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_074 0 243 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 0 121 122, g32p_row21_traceSegment_074_0000_0121, g32p_row21_traceSegment_074_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 243 15 15, g32p_row21_traceSegment_074_0243_0015, g32p_row21_traceSegment_074_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 273 15 15, g32p_row21_traceSegment_074_0273_0015, g32p_row21_traceSegment_074_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_074 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 243 30 30, g32p_row21_traceSegment_074_0243_0030, g32p_row21_traceSegment_074_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 303 15 15, g32p_row21_traceSegment_074_0303_0015, g32p_row21_traceSegment_074_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 348 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 333 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 333 15 16, g32p_row21_traceSegment_074_0333_0015, g32p_row21_traceSegment_074_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 303 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 303 30 31, g32p_row21_traceSegment_074_0303_0030, g32p_row21_traceSegment_074_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_074 243 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 243 60 61, g32p_row21_traceSegment_074_0243_0060, g32p_row21_traceSegment_074_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 364 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 364 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 364 15 15, g32p_row21_traceSegment_074_0364_0015, g32p_row21_traceSegment_074_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 394 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 394 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 394 15 16, g32p_row21_traceSegment_074_0394_0015, g32p_row21_traceSegment_074_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 364 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 364 30 31, g32p_row21_traceSegment_074_0364_0030, g32p_row21_traceSegment_074_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 425 15 15, g32p_row21_traceSegment_074_0425_0015, g32p_row21_traceSegment_074_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 455 15 16, g32p_row21_traceSegment_074_0455_0015, g32p_row21_traceSegment_074_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 425 30 31, g32p_row21_traceSegment_074_0425_0030, g32p_row21_traceSegment_074_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_074 364 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 364 61 61, g32p_row21_traceSegment_074_0364_0061, g32p_row21_traceSegment_074_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_074 243 243 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 243 121 122, g32p_row21_traceSegment_074_0243_0121, g32p_row21_traceSegment_074_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_074 0 486 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 0 243 243, g32p_row21_traceSegment_074_0000_0243, g32p_row21_traceSegment_074_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 486 15 15, g32p_row21_traceSegment_074_0486_0015, g32p_row21_traceSegment_074_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 531 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 516 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 516 15 15, g32p_row21_traceSegment_074_0516_0015, g32p_row21_traceSegment_074_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_074 486 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 486 30 30, g32p_row21_traceSegment_074_0486_0030, g32p_row21_traceSegment_074_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 546 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 561 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 546 30 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 546 15 15, g32p_row21_traceSegment_074_0546_0015, g32p_row21_traceSegment_074_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 576 15 16, g32p_row21_traceSegment_074_0576_0015, g32p_row21_traceSegment_074_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 546 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 546 30 31, g32p_row21_traceSegment_074_0546_0030, g32p_row21_traceSegment_074_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_074 486 121 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 486 60 61, g32p_row21_traceSegment_074_0486_0060, g32p_row21_traceSegment_074_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 607 15 15, g32p_row21_traceSegment_074_0607_0015, g32p_row21_traceSegment_074_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 637 15 16, g32p_row21_traceSegment_074_0637_0015, g32p_row21_traceSegment_074_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 607 30 31, g32p_row21_traceSegment_074_0607_0030, g32p_row21_traceSegment_074_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 668 15 15, g32p_row21_traceSegment_074_0668_0015, g32p_row21_traceSegment_074_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 698 15 16, g32p_row21_traceSegment_074_0698_0015, g32p_row21_traceSegment_074_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 668 30 31, g32p_row21_traceSegment_074_0668_0030, g32p_row21_traceSegment_074_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_074 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 607 61 61, g32p_row21_traceSegment_074_0607_0061, g32p_row21_traceSegment_074_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_074 486 243 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 486 121 122, g32p_row21_traceSegment_074_0486_0121, g32p_row21_traceSegment_074_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 729 15 15, g32p_row21_traceSegment_074_0729_0015, g32p_row21_traceSegment_074_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 759 15 15, g32p_row21_traceSegment_074_0759_0015, g32p_row21_traceSegment_074_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_074 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 729 30 30, g32p_row21_traceSegment_074_0729_0030, g32p_row21_traceSegment_074_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 789 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 804 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 789 30 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 789 15 15, g32p_row21_traceSegment_074_0789_0015, g32p_row21_traceSegment_074_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 819 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 819 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 819 15 16, g32p_row21_traceSegment_074_0819_0015, g32p_row21_traceSegment_074_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 789 61 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 789 30 31, g32p_row21_traceSegment_074_0789_0030, g32p_row21_traceSegment_074_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_074 729 121 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 729 60 61, g32p_row21_traceSegment_074_0729_0060, g32p_row21_traceSegment_074_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 850 15 15, g32p_row21_traceSegment_074_0850_0015, g32p_row21_traceSegment_074_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 880 15 16, g32p_row21_traceSegment_074_0880_0015, g32p_row21_traceSegment_074_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 850 30 31, g32p_row21_traceSegment_074_0850_0030, g32p_row21_traceSegment_074_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_074 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 911 15 15, g32p_row21_traceSegment_074_0911_0015, g32p_row21_traceSegment_074_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_074 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_074 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_074_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_074 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 941 15 16, g32p_row21_traceSegment_074_0941_0015, g32p_row21_traceSegment_074_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_074 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 911 30 31, g32p_row21_traceSegment_074_0911_0030, g32p_row21_traceSegment_074_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_074 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 850 61 61, g32p_row21_traceSegment_074_0850_0061, g32p_row21_traceSegment_074_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_074 729 243 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 729 121 122, g32p_row21_traceSegment_074_0729_0121, g32p_row21_traceSegment_074_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_074 486 486 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 486 243 243, g32p_row21_traceSegment_074_0486_0243, g32p_row21_traceSegment_074_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_074_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_074 0 972 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_074 0 486 486, g32p_row21_traceSegment_074_0000_0486, g32p_row21_traceSegment_074_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 74 = [0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_074_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_075 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 75 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_075_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 0 15 15, g32p_row21_traceSegment_075_0000_0015, g32p_row21_traceSegment_075_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 30 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 30 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 30 15 15, g32p_row21_traceSegment_075_0030_0015, g32p_row21_traceSegment_075_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_075 0 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 0 30 30, g32p_row21_traceSegment_075_0000_0030, g32p_row21_traceSegment_075_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 60 15 15, g32p_row21_traceSegment_075_0060_0015, g32p_row21_traceSegment_075_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 90 15 16, g32p_row21_traceSegment_075_0090_0015, g32p_row21_traceSegment_075_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 60 30 31, g32p_row21_traceSegment_075_0060_0030, g32p_row21_traceSegment_075_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_075 0 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 0 60 61, g32p_row21_traceSegment_075_0000_0060, g32p_row21_traceSegment_075_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 136 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 121 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 121 15 15, g32p_row21_traceSegment_075_0121_0015, g32p_row21_traceSegment_075_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 151 15 16, g32p_row21_traceSegment_075_0151_0015, g32p_row21_traceSegment_075_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 121 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 121 30 31, g32p_row21_traceSegment_075_0121_0030, g32p_row21_traceSegment_075_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 197 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 182 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 182 15 15, g32p_row21_traceSegment_075_0182_0015, g32p_row21_traceSegment_075_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 212 15 16, g32p_row21_traceSegment_075_0212_0015, g32p_row21_traceSegment_075_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 182 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 182 30 31, g32p_row21_traceSegment_075_0182_0030, g32p_row21_traceSegment_075_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_075 121 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 121 61 61, g32p_row21_traceSegment_075_0121_0061, g32p_row21_traceSegment_075_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_075 0 243 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 0 121 122, g32p_row21_traceSegment_075_0000_0121, g32p_row21_traceSegment_075_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 243 15 15, g32p_row21_traceSegment_075_0243_0015, g32p_row21_traceSegment_075_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 273 15 15, g32p_row21_traceSegment_075_0273_0015, g32p_row21_traceSegment_075_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_075 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 243 30 30, g32p_row21_traceSegment_075_0243_0030, g32p_row21_traceSegment_075_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 318 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 303 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 303 15 15, g32p_row21_traceSegment_075_0303_0015, g32p_row21_traceSegment_075_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 333 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 333 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 333 15 16, g32p_row21_traceSegment_075_0333_0015, g32p_row21_traceSegment_075_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 303 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 303 30 31, g32p_row21_traceSegment_075_0303_0030, g32p_row21_traceSegment_075_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_075 243 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 243 60 61, g32p_row21_traceSegment_075_0243_0060, g32p_row21_traceSegment_075_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 364 15 15, g32p_row21_traceSegment_075_0364_0015, g32p_row21_traceSegment_075_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 394 15 16, g32p_row21_traceSegment_075_0394_0015, g32p_row21_traceSegment_075_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 364 30 31, g32p_row21_traceSegment_075_0364_0030, g32p_row21_traceSegment_075_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 425 15 15, g32p_row21_traceSegment_075_0425_0015, g32p_row21_traceSegment_075_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 455 15 16, g32p_row21_traceSegment_075_0455_0015, g32p_row21_traceSegment_075_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 425 30 31, g32p_row21_traceSegment_075_0425_0030, g32p_row21_traceSegment_075_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_075 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 364 61 61, g32p_row21_traceSegment_075_0364_0061, g32p_row21_traceSegment_075_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_075 243 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 243 121 122, g32p_row21_traceSegment_075_0243_0121, g32p_row21_traceSegment_075_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_075 0 486 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 0 243 243, g32p_row21_traceSegment_075_0000_0243, g32p_row21_traceSegment_075_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 501 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 486 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 486 15 15, g32p_row21_traceSegment_075_0486_0015, g32p_row21_traceSegment_075_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 516 15 15, g32p_row21_traceSegment_075_0516_0015, g32p_row21_traceSegment_075_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_075 486 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 486 30 30, g32p_row21_traceSegment_075_0486_0030, g32p_row21_traceSegment_075_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 546 15 15, g32p_row21_traceSegment_075_0546_0015, g32p_row21_traceSegment_075_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 576 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 576 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 576 15 16, g32p_row21_traceSegment_075_0576_0015, g32p_row21_traceSegment_075_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 546 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 546 30 31, g32p_row21_traceSegment_075_0546_0030, g32p_row21_traceSegment_075_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_075 486 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 486 60 61, g32p_row21_traceSegment_075_0486_0060, g32p_row21_traceSegment_075_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 607 15 15, g32p_row21_traceSegment_075_0607_0015, g32p_row21_traceSegment_075_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 637 15 16, g32p_row21_traceSegment_075_0637_0015, g32p_row21_traceSegment_075_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 607 30 31, g32p_row21_traceSegment_075_0607_0030, g32p_row21_traceSegment_075_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 668 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 683 15 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 668 30 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 668 15 15, g32p_row21_traceSegment_075_0668_0015, g32p_row21_traceSegment_075_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 698 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 713 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 698 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 698 15 16, g32p_row21_traceSegment_075_0698_0015, g32p_row21_traceSegment_075_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 668 61 = [4, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 668 30 31, g32p_row21_traceSegment_075_0668_0030, g32p_row21_traceSegment_075_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_075 607 122 = [4, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 607 61 61, g32p_row21_traceSegment_075_0607_0061, g32p_row21_traceSegment_075_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_075 486 243 = [7, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 486 121 122, g32p_row21_traceSegment_075_0486_0121, g32p_row21_traceSegment_075_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 729 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 744 15 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 729 30 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 729 15 15, g32p_row21_traceSegment_075_0729_0015, g32p_row21_traceSegment_075_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 774 15 = [2, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 759 30 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 759 15 15, g32p_row21_traceSegment_075_0759_0015, g32p_row21_traceSegment_075_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_075 729 60 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 729 30 30, g32p_row21_traceSegment_075_0729_0030, g32p_row21_traceSegment_075_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 789 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 804 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 789 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 789 15 15, g32p_row21_traceSegment_075_0789_0015, g32p_row21_traceSegment_075_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 819 15 16, g32p_row21_traceSegment_075_0819_0015, g32p_row21_traceSegment_075_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 789 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 789 30 31, g32p_row21_traceSegment_075_0789_0030, g32p_row21_traceSegment_075_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_075 729 121 = [8, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 729 60 61, g32p_row21_traceSegment_075_0729_0060, g32p_row21_traceSegment_075_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 850 15 15, g32p_row21_traceSegment_075_0850_0015, g32p_row21_traceSegment_075_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 880 15 16, g32p_row21_traceSegment_075_0880_0015, g32p_row21_traceSegment_075_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 850 30 31, g32p_row21_traceSegment_075_0850_0030, g32p_row21_traceSegment_075_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 911 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 926 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_075 911 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 911 15 15, g32p_row21_traceSegment_075_0911_0015, g32p_row21_traceSegment_075_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_075 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_075 956 16 = [4] := by
  decide +kernel

private theorem g32p_row21_traceSegment_075_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_075 941 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 941 15 16, g32p_row21_traceSegment_075_0941_0015, g32p_row21_traceSegment_075_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_075 911 61 = [4, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 911 30 31, g32p_row21_traceSegment_075_0911_0030, g32p_row21_traceSegment_075_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_075 850 122 = [4, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 850 61 61, g32p_row21_traceSegment_075_0850_0061, g32p_row21_traceSegment_075_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_075 729 243 = [12, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 729 121 122, g32p_row21_traceSegment_075_0729_0121, g32p_row21_traceSegment_075_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_075 486 486 = [19, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 486 243 243, g32p_row21_traceSegment_075_0486_0243, g32p_row21_traceSegment_075_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_075_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_075 0 972 = [24, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_075 0 486 486, g32p_row21_traceSegment_075_0000_0486, g32p_row21_traceSegment_075_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 75 = [24, 3, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_075_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_076 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 76 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_076_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 15 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 0 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 0 15 15, g32p_row21_traceSegment_076_0000_0015, g32p_row21_traceSegment_076_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 30 15 15, g32p_row21_traceSegment_076_0030_0015, g32p_row21_traceSegment_076_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_076 0 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 0 30 30, g32p_row21_traceSegment_076_0000_0030, g32p_row21_traceSegment_076_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 60 15 15, g32p_row21_traceSegment_076_0060_0015, g32p_row21_traceSegment_076_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 90 15 16, g32p_row21_traceSegment_076_0090_0015, g32p_row21_traceSegment_076_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 60 30 31, g32p_row21_traceSegment_076_0060_0030, g32p_row21_traceSegment_076_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_076 0 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 0 60 61, g32p_row21_traceSegment_076_0000_0060, g32p_row21_traceSegment_076_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 121 15 15, g32p_row21_traceSegment_076_0121_0015, g32p_row21_traceSegment_076_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 151 15 16, g32p_row21_traceSegment_076_0151_0015, g32p_row21_traceSegment_076_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 121 30 31, g32p_row21_traceSegment_076_0121_0030, g32p_row21_traceSegment_076_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 182 15 15, g32p_row21_traceSegment_076_0182_0015, g32p_row21_traceSegment_076_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 212 15 16, g32p_row21_traceSegment_076_0212_0015, g32p_row21_traceSegment_076_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 182 30 31, g32p_row21_traceSegment_076_0182_0030, g32p_row21_traceSegment_076_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_076 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 121 61 61, g32p_row21_traceSegment_076_0121_0061, g32p_row21_traceSegment_076_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_076 0 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 0 121 122, g32p_row21_traceSegment_076_0000_0121, g32p_row21_traceSegment_076_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 243 15 15, g32p_row21_traceSegment_076_0243_0015, g32p_row21_traceSegment_076_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 273 15 15, g32p_row21_traceSegment_076_0273_0015, g32p_row21_traceSegment_076_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_076 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 243 30 30, g32p_row21_traceSegment_076_0243_0030, g32p_row21_traceSegment_076_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 303 15 = [1, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 303 30 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 303 15 15, g32p_row21_traceSegment_076_0303_0015, g32p_row21_traceSegment_076_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 333 15 16, g32p_row21_traceSegment_076_0333_0015, g32p_row21_traceSegment_076_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 303 61 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 303 30 31, g32p_row21_traceSegment_076_0303_0030, g32p_row21_traceSegment_076_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_076 243 121 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 243 60 61, g32p_row21_traceSegment_076_0243_0060, g32p_row21_traceSegment_076_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 364 15 15, g32p_row21_traceSegment_076_0364_0015, g32p_row21_traceSegment_076_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 394 15 16, g32p_row21_traceSegment_076_0394_0015, g32p_row21_traceSegment_076_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 364 30 31, g32p_row21_traceSegment_076_0364_0030, g32p_row21_traceSegment_076_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 425 15 15, g32p_row21_traceSegment_076_0425_0015, g32p_row21_traceSegment_076_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 455 15 16, g32p_row21_traceSegment_076_0455_0015, g32p_row21_traceSegment_076_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 425 30 31, g32p_row21_traceSegment_076_0425_0030, g32p_row21_traceSegment_076_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_076 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 364 61 61, g32p_row21_traceSegment_076_0364_0061, g32p_row21_traceSegment_076_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_076 243 243 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 243 121 122, g32p_row21_traceSegment_076_0243_0121, g32p_row21_traceSegment_076_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_076 0 486 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 0 243 243, g32p_row21_traceSegment_076_0000_0243, g32p_row21_traceSegment_076_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 486 15 15, g32p_row21_traceSegment_076_0486_0015, g32p_row21_traceSegment_076_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 516 15 15, g32p_row21_traceSegment_076_0516_0015, g32p_row21_traceSegment_076_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_076 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 486 30 30, g32p_row21_traceSegment_076_0486_0030, g32p_row21_traceSegment_076_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 546 15 15, g32p_row21_traceSegment_076_0546_0015, g32p_row21_traceSegment_076_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 576 15 16, g32p_row21_traceSegment_076_0576_0015, g32p_row21_traceSegment_076_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 546 30 31, g32p_row21_traceSegment_076_0546_0030, g32p_row21_traceSegment_076_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_076 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 486 60 61, g32p_row21_traceSegment_076_0486_0060, g32p_row21_traceSegment_076_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 607 15 15, g32p_row21_traceSegment_076_0607_0015, g32p_row21_traceSegment_076_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 637 15 16, g32p_row21_traceSegment_076_0637_0015, g32p_row21_traceSegment_076_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 607 30 31, g32p_row21_traceSegment_076_0607_0030, g32p_row21_traceSegment_076_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 668 15 15, g32p_row21_traceSegment_076_0668_0015, g32p_row21_traceSegment_076_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 698 15 16, g32p_row21_traceSegment_076_0698_0015, g32p_row21_traceSegment_076_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 668 30 31, g32p_row21_traceSegment_076_0668_0030, g32p_row21_traceSegment_076_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_076 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 607 61 61, g32p_row21_traceSegment_076_0607_0061, g32p_row21_traceSegment_076_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_076 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 486 121 122, g32p_row21_traceSegment_076_0486_0121, g32p_row21_traceSegment_076_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 729 15 15, g32p_row21_traceSegment_076_0729_0015, g32p_row21_traceSegment_076_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 759 15 15, g32p_row21_traceSegment_076_0759_0015, g32p_row21_traceSegment_076_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_076 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 729 30 30, g32p_row21_traceSegment_076_0729_0030, g32p_row21_traceSegment_076_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 789 15 15, g32p_row21_traceSegment_076_0789_0015, g32p_row21_traceSegment_076_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 819 15 16, g32p_row21_traceSegment_076_0819_0015, g32p_row21_traceSegment_076_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 789 30 31, g32p_row21_traceSegment_076_0789_0030, g32p_row21_traceSegment_076_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_076 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 729 60 61, g32p_row21_traceSegment_076_0729_0060, g32p_row21_traceSegment_076_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 850 15 15, g32p_row21_traceSegment_076_0850_0015, g32p_row21_traceSegment_076_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 880 15 16, g32p_row21_traceSegment_076_0880_0015, g32p_row21_traceSegment_076_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 850 30 31, g32p_row21_traceSegment_076_0850_0030, g32p_row21_traceSegment_076_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_076 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 911 15 15, g32p_row21_traceSegment_076_0911_0015, g32p_row21_traceSegment_076_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_076 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_076 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_076_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_076 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 941 15 16, g32p_row21_traceSegment_076_0941_0015, g32p_row21_traceSegment_076_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_076 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 911 30 31, g32p_row21_traceSegment_076_0911_0030, g32p_row21_traceSegment_076_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_076 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 850 61 61, g32p_row21_traceSegment_076_0850_0061, g32p_row21_traceSegment_076_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_076 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 729 121 122, g32p_row21_traceSegment_076_0729_0121, g32p_row21_traceSegment_076_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_076 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 486 243 243, g32p_row21_traceSegment_076_0486_0243, g32p_row21_traceSegment_076_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_076_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_076 0 972 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_076 0 486 486, g32p_row21_traceSegment_076_0000_0486, g32p_row21_traceSegment_076_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 76 = [1, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_076_0000_0972

end HodgeLean.Foundations.Program

end
end
